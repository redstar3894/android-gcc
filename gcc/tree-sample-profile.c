/* Sample profile support in GCC.
   Copyright (C) 2008
   Free Software Foundation, Inc.
   Contributed by Paul Yuan (yingbo.com@gmail.com)
              and Vinodha Ramasamy (vinodha@google.com)

This file is part of GCC.
GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

/* References:
   [1] "Feedback-directed Optimizations in GCC with Estimated Edge Profiles
        from Hardware Event Sampling", Vinodha Ramasamy, Paul Yuan, Dehao Chen,
        and Robert Hundt; GCC Summit 2008.
*/

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "hashtab.h"
#include "rtl.h"
#include "expr.h"
#include "basic-block.h"
#include "output.h"
#include "flags.h"
#include "langhooks.h"
#include "recog.h"
#include "optabs.h"
#include "ggc.h"
#include "tree-flow.h"
#include "diagnostic.h"
#include "coverage.h"
#include "tree.h"
#include "gcov-io.h"
#include "cgraph.h"
#include "cfgloop.h"
#include "timevar.h"
#include "tree-pass.h"
#include "toplev.h"
#include "params.h"
#include "gimple.h"
#include "profile.h"
#include "tree-sample-profile.h"
#include "opts.h"
#include "l-ipo.h"
#include "value-prof.h"

#define DEFAULT_SAMPLE_DATAFILE "sp.data"
#define MAX_LINENUM_CHARS         10
#define FB_INLINE_MAX_STACK       200
#define MAX_LINES_PER_BASIC_BLOCK 500
#define MIN_SAMPLE_BB_COUNT       5

#define DISCRIM(x) (PARAM_VALUE (PARAM_SAMPLEFDO_USE_DISCRIMINATORS) ? (x) : 0)

/* File name of sample file.  */
const char *sample_data_name = NULL;

/* Hashtable to hold elements with <filename_ptr, line_num, freq> 
   from sample file.  */
static htab_t sp_htab;
/* Buffer to hold elements inserted into sp_htab.  */
struct sample_freq_detail *sample_buf;

/* Hashtable to hold elements for inlined function samples with 
   <inline_stack_ptr, filename_ptr, line_num, freq>.
   <inline_stack_ptr> format:
   <func_name>:<stack[n].filename>:<stack[n].line_num>:
   <stack[n-1].filename>:<stack[n-1].line_num>:...
   <stack[0].filename>:<stack[0].line_num>.  */
static htab_t sp_inline_htab;

static htab_t sp_indirect_htab;

static htab_t sp_funcname_htab;
/* Buffer to hold elements inserted into sp_inline_htab.  */
struct sample_inline_freq *inline_sample_buf;

/* Number of samples read from sample file.  */
static unsigned long long sp_num_samples;

/* Maximum count/freq in the sample file.  */
static gcov_type sp_max_count;

/* Assist for the reading of sample file.  */
static struct profile prog_unit;

static struct gcov_ctr_summary *sp_profile_info;

/* Print hash table statistics for HTAB.  */
static void
print_hash_table_statistics (htab_t htab)
{
  if (!dump_file)
    return;
  fprintf (dump_file,
           "sample_profile hash - size: %ld, elements %ld, collisions: %f\n", 
           (long) htab_size (htab), (long) htab_elements (htab),
           htab_collisions (htab));
}


/* Dump CFG profile information into output file named PNAME. File format:
   **********************************************
   ;;n_basic_blocks n_edges count function_name1
   e1->src->index e1->dest->index pw probability count
   ...
   ;;n_basic_blocks n_edges count function_name1
   e1->src->index e1->dest->index pw probability count
   ...
   ...
   **********************************************
   pw (percentage weight) is a metric for overlap measurement.  */
static void
dump_cfg_profile (const char *pname)
{
  FILE *prof_compare_file;
  basic_block bb;
  edge e;
  edge_iterator ei;
  /* Sum of edge frequencies.  */
  int sum_edge_freq = 0;

  prof_compare_file = fopen (pname, "a");
  if (!prof_compare_file)
    {
      inform (0, "Cannot create output file %s to dump CFG profile", pname);
      return;
    }

  fprintf (prof_compare_file, ";;%d %d " HOST_WIDEST_INT_PRINT_DEC " %s\n",
	   n_basic_blocks, n_edges, ENTRY_BLOCK_PTR->count,
	   lang_hooks.decl_printable_name (current_function_decl, 2));

  FOR_BB_BETWEEN (bb, ENTRY_BLOCK_PTR, EXIT_BLOCK_PTR, next_bb)
    FOR_EACH_EDGE (e, ei, bb->succs)
      sum_edge_freq += e->src->frequency * e->probability / REG_BR_PROB_BASE;

  FOR_BB_BETWEEN (bb, ENTRY_BLOCK_PTR, EXIT_BLOCK_PTR, next_bb)
    {
      FOR_EACH_EDGE (e, ei, bb->succs)
        {
          int efreq = e->src->frequency * e->probability / REG_BR_PROB_BASE;
          if (sum_edge_freq)
  	    fprintf (prof_compare_file,
	             "%d %d %f %d " HOST_WIDEST_INT_PRINT_DEC "\n", bb->index,
		     e->dest->index, (float) efreq / sum_edge_freq,
		     e->probability, e->count);
          else
	    fprintf (prof_compare_file,
		     "%d %d 0.0 %d " HOST_WIDEST_INT_PRINT_DEC "\n", bb->index,
		     e->dest->index, e->probability, e->count);
        }
    }

  fclose (prof_compare_file);
}

/* extract the path info of NAME, and return the file name.  */
static const char *realname (const char *name) {
  const char *c;
  for (c = name; *c; c++) {
    if (*c == '/') name = c+1;
  }
  return name;
}

static hashval_t
sp_indirect_hash (const void *fb_info)
{
  const struct sample_indirect_call *si =
    (const struct sample_indirect_call *) fb_info;
  hashval_t h = 0x9e3779b9;

  return iterative_hash (si->func_name, strlen (si->func_name), h);
}

static int
sp_indirect_eq (const void *p, const void *q)
{
  const struct sample_indirect_call *a =
      (const struct sample_indirect_call *) p;

  const struct sample_indirect_call *b =
      (const struct sample_indirect_call *) q;

  return !strcmp(a->func_name, b->func_name);
}

/* Functions used for hash table to store samples.
   key = string base_filename:line_num.  */

/* Create a hash string with FILENAME, LINE_NUM, DISCRIMINATOR, and
   FUNCNAME.  */
static hashval_t
create_hash_string (const char *filename, int line_num, int discriminator)
{
  /* An arbitrary initial value borrowed from hashtab.c.  */
  hashval_t h = 0x9e3779b9;
  filename = realname (filename);
  h = iterative_hash (filename, strlen (filename), h);
  h = iterative_hash (&line_num, sizeof (line_num), h);
  h = iterative_hash (&discriminator, sizeof(discriminator), h);
  return h;
}


/* Hash function for struct sample_freq_detail entry.  */
static hashval_t
sp_info_hash (const void *fb_info)
{
  const struct sample_freq_detail *sp =
      (const struct sample_freq_detail *) fb_info;

  gcc_assert (sp->line_num >= 0);

  return create_hash_string (realname (sp->filename), sp->line_num,
                             sp->discriminator);
}


/* Check if two elements of type sample_freq_detail pointed to by P and Q are
   equal.  */
static int
sp_info_eq (const void *p, const void *q)
{
  const struct sample_freq_detail *a =
      (const struct sample_freq_detail *) p;

  const struct sample_freq_detail *b =
      (const struct sample_freq_detail *) q;

  return (a->line_num == b->line_num)
    && (a->discriminator == b->discriminator)
    && (!strcmp (realname (a->filename), realname (b->filename)));
}

/* Compute hash value for INLINE_INFO.  */
static hashval_t
sp_inline_info_hash (const void *inline_info)
{
  /* An arbitrary initial value borrowed from hashtab.c.  */
  hashval_t h = 0x9e3779b9;
  const struct sample_inline_freq *i_info =
      (const struct sample_inline_freq *) inline_info;
  int depth = i_info->depth;
  int i = 0;

  while (i < depth)
    {
       h = iterative_hash (realname (i_info->inline_stack[i].loc.file),
                           strlen (realname (i_info->inline_stack[i].loc.file)),
                                             h);
       h = iterative_hash (&(i_info->inline_stack[i].loc.line),
                           sizeof (i_info->inline_stack[i].loc.line), h);
       i++;
    }
  h = iterative_hash (realname (i_info->filename),
                      strlen (realname (i_info->filename)), h);
  h = iterative_hash (&(i_info->line_num), sizeof (i_info->line_num), h);
  h = iterative_hash (&(i_info->discriminator),
		      sizeof (i_info->discriminator), h);

  return h;
}

/* Return non-zero if the two sample_inline_freq elements pointed to by P and
   Q are equal, 0 otherwise.  */
static int
sp_inline_info_eq (const void *p, const void *q)
{
  const struct sample_inline_freq *a =
      (const struct sample_inline_freq *) p;

  const struct sample_inline_freq *b =
      (const struct sample_inline_freq *) q;

  int i = 0;

  if (a->line_num != b->line_num)
    return 0;

  if (a->discriminator != b->discriminator)
    return 0;

  /* Compare the inline stacks.  */
  if (a->depth != b->depth)
    return 0;

  while (i < a->depth)
    {
      if ((a->inline_stack[i].loc.line != b->inline_stack[i].loc.line)
          || strcmp (realname (a->inline_stack[i].loc.file),
                     realname (b->inline_stack[i].loc.file)))
        return 0;
      i++;
    }

  return !strcmp (realname (a->filename), realname (b->filename));
}

/* Usage model: All elements in the hash table are deleted only at time of hash
   table deletion. INLINE_STACK is shared among multiple elements, so use the
   IS_FIRST field to determine when to free it. Also, if the num of value
   profiles are more than 0, free the memory used to store value profile.  */

static void
sp_inline_info_del (void *p)
{
  struct sample_inline_freq *a = (struct sample_inline_freq *) p;

  if (a->is_first)
    free (a->inline_stack);

  if (a->num_value > 0)
    free (a->values);
}

/* Free the memory of value profile if there are any.  */

static void
sp_info_del (void *p)
{
  struct sample_freq_detail *a = (struct sample_freq_detail *) p;

  if (a->num_value > 0)
    free (a->values);
}

/* Structure to store the mapping between the new function name and the
   original function name.  */

#define MAX_FUNC_NAME_LENGTH 2048

struct name_mapping
{
  char new_name[MAX_FUNC_NAME_LENGTH];
  char orig_name[MAX_FUNC_NAME_LENGTH];
};

/* Compute Hash Value for function name. The hash is only computed on the new
   function name.  */

static hashval_t
sp_funcname_hash (const void *name)
{
  const struct name_mapping *mapping =
    (const struct name_mapping *)name;
  hashval_t h = 0x9e3779b9;
  h = iterative_hash (mapping->new_name,
                      strlen (mapping->new_name), h);
  return h;
}

/* Return non-Zero if the function names are equal. Only the new name is
   compared here.  */

static int
sp_funcname_eq (const void *p, const void *q)
{
  const struct name_mapping *m1 = (const struct name_mapping *)p;
  const struct name_mapping *m2 = (const struct name_mapping *)q;
  return !strcmp(m1->new_name, m2->new_name);
}

/* Array to store the function name mapping.
   TODO: This is ugly... however when I use xmalloc, it generate the random
         error... Need to be converted to dynamic memory allocation later.   */

#define MAX_FUNC_MAPPINGS 65536

static struct name_mapping funcname_buf[MAX_FUNC_MAPPINGS];
static int funcname_buf_size = 0;

/* External function to add a mapping between function names.  */

void sp_add_funcname_mapping (const char *new_name, const char *orig_name)
{
  struct name_mapping **slot;
  strcpy(funcname_buf[funcname_buf_size].new_name, new_name);
  strcpy(funcname_buf[funcname_buf_size].orig_name, orig_name);
  slot = (struct name_mapping **)
    htab_find_slot (sp_funcname_htab, &funcname_buf[funcname_buf_size], INSERT);
  if (!*slot)
    {
      gcc_assert (funcname_buf_size < MAX_FUNC_MAPPINGS);
      *slot = &funcname_buf[funcname_buf_size++];
    }
  else
    {
      inform (0, "Duplicate entry of function name mapping");
    }
}

/* External function to get the original function name either through name
   itself or through name mapping.  */

const char *sp_get_real_funcname (const char *name)
{
  struct name_mapping nm, *pnm;
  if (!flag_dyn_ipa)
    return name;
  strcpy (nm.new_name, name);
  pnm = (struct name_mapping *)
      htab_find (sp_funcname_htab, (void *) &nm);

  if (!pnm)
    return name;
  else
    return pnm->orig_name;
}

/* Get and store the inline stack corresponding to STMT into the output
   parameter STACK.  */
static int
sp_get_inline_stack (gimple stmt, struct expanded_inline_location *stack)
{
  tree block = gimple_block (stmt);
  unsigned int i = 0, last_loc = 0;
  if (!block || (TREE_CODE (block) != BLOCK))
    return 0;
  for ( block = BLOCK_SUPERCONTEXT (block);
        block && (TREE_CODE (block) == BLOCK);
        block = BLOCK_SUPERCONTEXT (block)) {
    if (!BLOCK_SOURCE_LOCATION (block) > 0 
        || BLOCK_SOURCE_LOCATION (block) == last_loc)
      continue;
    last_loc = BLOCK_SOURCE_LOCATION (block);
    stack[i].loc = expand_location (last_loc);
    stack[i++].discriminator = get_discriminator_from_locus (last_loc);
  }
  return i;
}

/* Build a hashtab element to state that FUNC_NAME has an indirect
   call edge of weight COUNT to the TARGET function.  */

static void
sp_add_indirect_call (const char *func_name, const char *target,
                      gcov_type count)
{
  struct sample_indirect_call ic;
  struct sample_indirect_call *entry;
  struct sample_indirect_call **slot;
  unsigned i;
  ic.func_name = func_name;

  slot = (struct sample_indirect_call **)
         htab_find_slot (sp_indirect_htab, (void *) &ic, INSERT);

  if (!*slot) {
    *slot = (struct sample_indirect_call *)
                 xmalloc(sizeof(struct sample_indirect_call));
    (*slot)->func_name = func_name;
    (*slot)->num_values = 0;
  }
  entry = *slot;
  if (entry->num_values == MAX_IND_FUNCS)
    return;
  for (i = 0; i < entry->num_values; i++) {
    if (!strcmp(target, entry->targets[i])) {
      entry->count[i] += count;
      return;
    }
  }
  entry->targets[entry->num_values] = 0;
  entry->targets[entry->num_values++] = target;
}

/* Read in the FUNC_NAME, return the hashtab that contains the
   indirect calls from this function.  */

struct sample_indirect_call *
sp_get_indirect_calls (const char *func_name)
{
  struct sample_indirect_call ic;
  ic.func_name = func_name;

  return (struct sample_indirect_call *)
         htab_find (sp_indirect_htab, (void *) &ic);
}

/* Read file header from input file INFILE into PROG_UNIT. Return 0 if
   successful, -1 otherwise.  */
static int
read_file_header (FILE *infile, struct profile *prog_unit)
{
  if (fread (&(prog_unit->fb_hdr), 1, sizeof (struct fb_sample_hdr), infile)
      != sizeof (struct fb_sample_hdr))
    return -1;
  return 0;
}

/* Read string table from INFILE into PROG_UNIT. Return 0 if successful, -1
   otherwise.  */
static int
read_string_table (FILE *infile, struct profile *prog_unit)
{
  unsigned long long str_table_size;

  if (fseek (infile, (prog_unit->fb_hdr).fb_str_table_offset, SEEK_SET) != 0)
    return -1;

  str_table_size = prog_unit->fb_hdr.fb_str_table_size;

  prog_unit->str_table = (char *) xmalloc (str_table_size);
  if (!(prog_unit->str_table))
    return -1;
  if (fread (prog_unit->str_table, 1, str_table_size, infile) !=
      str_table_size)
    return -1;

  return 0;
}

/* Read function header with index I from INFILE into FUNC_HDR. PROG_UNIT holds
   file header and string table. Return 0 if successful, -1 otherwise.  */
static int
read_function_header (FILE *infile, unsigned int i,
		      struct profile *prog_unit,
		      struct func_sample_hdr *func_hdr)
{
  struct fb_sample_hdr *fb_hdr = &(prog_unit->fb_hdr);
  unsigned int func_hdr_size;
  unsigned int offset;

  gcc_assert (i <= fb_hdr->fb_func_hdr_num);
  func_hdr_size = fb_hdr->fb_func_hdr_ent_size;
  offset = i * func_hdr_size;

  if (fseek (infile, fb_hdr->fb_func_hdr_offset + offset, SEEK_SET) != 0)
    return -1;
  if (fread (func_hdr, 1, func_hdr_size, infile) != func_hdr_size)
    return -1;
  return 0;
}

static int
get_discriminator (gimple stmt)
{
  location_t loc = gimple_location (stmt);
  if (loc == UNKNOWN_LOCATION)
    return -1;
  return get_discriminator_from_locus (loc);
}

/* Get the inline stack of STMT, and write it to the STACK with offset of IDX.
   Return the new offset. Returns -1 on error.  */
static int
get_stack_trace_by_stmt (gimple stmt, struct expanded_inline_location *stack,
                         int idx)
{
  tree block;
  unsigned int last_loc = 0;
  if (!stmt)
    return -1;
  block = gimple_block (stmt);
  if (!block || TREE_CODE (block) != BLOCK || !gimple_location(stmt))
    return -1;

  stack[idx].loc = expand_location (gimple_location (stmt));
  stack[idx++].discriminator = get_discriminator(stmt);
  for ( block = BLOCK_SUPERCONTEXT (block);
        block && (TREE_CODE (block) == BLOCK);
        block = BLOCK_SUPERCONTEXT (block)) {
    if (! BLOCK_SOURCE_LOCATION (block) > 0 ||
        BLOCK_SOURCE_LOCATION (block) == last_loc)
      continue;
    last_loc = BLOCK_SOURCE_LOCATION (block);
    gcc_assert (idx < FB_INLINE_MAX_STACK);
    stack[idx].loc = expand_location (last_loc);
    stack[idx++].discriminator = get_discriminator_from_locus(last_loc);
  }
  return idx;
}

/* Get the total execution count of an inlined function.  */
unsigned long long
get_total_count (gimple stmt, const char *func_name)
{
  int idx = 0;
  struct expanded_inline_location stack[FB_INLINE_MAX_STACK];
  struct sample_inline_freq inline_loc;
  struct sample_inline_freq *inline_htab_entry;

  idx = get_stack_trace_by_stmt (stmt, stack, 0);
  if (idx == -1)
    return 0;

  inline_loc.depth = idx;
  inline_loc.inline_stack = stack;
  inline_loc.func_name = func_name;
  inline_loc.filename = "";
  inline_loc.line_num = 0;
  inline_loc.discriminator = 0;

  inline_htab_entry = (struct sample_inline_freq *)
         htab_find (sp_inline_htab, (void *) &inline_loc);

  if (!inline_htab_entry)
    return 0;

  return inline_htab_entry->freq;
}

/* Get the total execution count of an inlined function.  */
unsigned long long
get_total_count_edge (struct cgraph_edge *edge, const char *func_name)
{
  int idx = 0;
  gimple stmt = edge->call_stmt;
  struct expanded_inline_location stack[FB_INLINE_MAX_STACK];
  struct sample_inline_freq inline_loc;
  struct sample_inline_freq *inline_htab_entry;

  idx = get_stack_trace_by_stmt (stmt, stack, 0);
  if (idx == -1)
    return 0;

  while (edge->caller->global.inlined_to)
    {
      edge = edge->caller->callers;
      stmt = edge->call_stmt;
      idx = get_stack_trace_by_stmt (stmt, stack, idx);
      if (idx == -1)
        return 0;
    }

  inline_loc.depth = idx;
  inline_loc.inline_stack = stack;
  inline_loc.func_name = func_name;
  inline_loc.filename = "";
  inline_loc.line_num = 0;
  inline_loc.discriminator = 0;

  inline_htab_entry = (struct sample_inline_freq *)
         htab_find (sp_inline_htab, (void *) &inline_loc);

  if (!inline_htab_entry)
    return 0;

  return inline_htab_entry->freq;
}

/* Read inline sections for the function header FUNC_HDR in file INFILE.
   PROG_UNIT holds file header information and string table. Input parameter
   NUM_SAMPLES specifies the number of samples read so far. Return the
   total number of samples read, including NUM_SAMPLES.  */
static unsigned long long
read_inline_function (FILE *infile, struct profile *prog_unit,
                      struct func_sample_hdr *func_hdr,
                      unsigned long long num_samples)
{
  unsigned long long inline_hdr_offset, profile_offset;
  unsigned long long j, k;
  unsigned long long num_lines;
  struct func_sample_hdr inline_func_hdr;
  struct fb_sample_hdr *fb_hdr = &(prog_unit->fb_hdr);
  unsigned int func_hdr_size = fb_hdr->fb_func_hdr_ent_size;
  unsigned long long num_inlines = func_hdr->func_num_inline_entries;
  unsigned long long curr_num_samples = num_samples;

  for (k = 0; k < num_inlines; k++)
    {
      int i = 0;
      struct expanded_inline_location *stack_buf;
      struct fb_info_inline_stack_entry stack_entry[FB_INLINE_MAX_STACK];
      size_t stack_entry_size = sizeof (struct fb_info_inline_stack_entry);
      int inline_depth;
      struct sample_inline_freq **slot;

      inline_hdr_offset = 
          fb_hdr->fb_func_hdr_offset + func_hdr->func_inline_hdr_offset
          + fb_hdr->fb_func_hdr_num * func_hdr_size + k * func_hdr_size;
      if (fseek (infile, inline_hdr_offset, SEEK_SET) != 0)
        {
          error ("read_inline_function(): fseek inline_func_hdr error.");
          return curr_num_samples;
        }
      if (fread (&inline_func_hdr, 1, func_hdr_size, infile) != func_hdr_size)
        {
          error ("read_inline_function(): fread inline_func_hdr error.");
          return curr_num_samples;
        }

      inline_depth = inline_func_hdr.inline_depth;
      num_lines = inline_func_hdr.func_num_freq_entries;

      if (num_lines == 0)
        continue;

      profile_offset = prog_unit->fb_hdr.fb_profile_offset
          + inline_func_hdr.inline_stack_offset;

      stack_buf = (struct expanded_inline_location *)
          xcalloc (inline_func_hdr.inline_depth,
                   sizeof (struct expanded_inline_location));

      /* Seek to beginning of the inline stack.  */
      if (fseek (infile, profile_offset, SEEK_SET) != 0)
        {
          error ("read_inline_function(): fseek profile_data error.");
          return curr_num_samples;
        }

      gcc_assert (inline_depth < FB_INLINE_MAX_STACK);
      gcc_assert (inline_depth > 0);
      if (fread (&stack_entry, stack_entry_size, inline_depth, infile)
          != (size_t) inline_depth)
        {
          error ("read_inline_function(): fread profile_data error.");
          return curr_num_samples;
        }
      /* Set up stack buffer.  */
      i = 0;
      while (i < inline_depth)
        {
          /* Stack stored in reverse in datafile.  */
          stack_buf[inline_depth - i - 1].loc.file =
              &(prog_unit->str_table[stack_entry[i].filename_offset]);
          stack_buf[inline_depth - i - 1].loc.line =  stack_entry[i].line_num;
          stack_buf[inline_depth - i - 1].discriminator
              = stack_entry[i].discriminator;
          i++;
        }

      /* The last entry in inline_sample_buf presents the total sample of the
         inlined function.  */
      inline_sample_buf = (struct sample_inline_freq *)
          xcalloc (num_lines + 1, sizeof (struct sample_inline_freq));

      /* Insert the total sample of the callsite */
      inline_sample_buf[num_lines].func_name = 
          &(prog_unit->str_table[inline_func_hdr.func_name_index]);
      inline_sample_buf[num_lines].depth = inline_depth;
      inline_sample_buf[num_lines].inline_stack = stack_buf;
      inline_sample_buf[num_lines].filename = "";
      inline_sample_buf[num_lines].line_num = 0;
      inline_sample_buf[num_lines].discriminator = 0;
      inline_sample_buf[num_lines].freq = inline_func_hdr.total_samples;
      inline_sample_buf[num_lines].is_first = false;

      /* Insert new sample into inline hash table. */
      slot = (struct sample_inline_freq **)
          htab_find_slot (sp_inline_htab, &inline_sample_buf[num_lines], INSERT);
      if (*slot)
        inform (0, "Duplicate entry of callstack");
      else
        *slot = &inline_sample_buf[num_lines];

      for (j = 0; j < num_lines; ++j)
        {
          struct fb_info_freq sample;

          /* Find the offset of the frequency profile.  */
          profile_offset = prog_unit->fb_hdr.fb_profile_offset
              + inline_func_hdr.func_profile_offset + j * sizeof (sample);
          if (fseek (infile, profile_offset, SEEK_SET) != 0)
            {
              error ("read_inline_function(): fseek profile_data error.");
              return curr_num_samples;
            }

          if (fread (&sample, 1, sizeof (sample), infile) != sizeof (sample))
            {
              error ("read_inline_function(): fread profile_data error.");
              return curr_num_samples;
            }

	  inline_sample_buf[j].func_name =
              &(prog_unit->str_table[inline_func_hdr.func_name_index]);
          inline_sample_buf[j].depth = inline_depth;
          inline_sample_buf[j].inline_stack = stack_buf;
	  inline_sample_buf[j].filename =
              &(prog_unit->str_table[sample.filename_offset]);
	  inline_sample_buf[j].line_num = sample.line_num;
	  inline_sample_buf[j].discriminator = DISCRIM (sample.discriminator);
	  inline_sample_buf[j].freq = sample.freq;
          inline_sample_buf[j].num_instr = sample.num_instr;
          inline_sample_buf[j].num_value = sample.num_value;

          /* Read in the value profiles if available.  */
          if (sample.num_value > 0) {
            unsigned long long k;
            struct fb_info_hist *hist_buf = (struct fb_info_hist *)
                alloca (sample.num_value * sizeof (struct fb_info_hist));

            /* Find the offset of the value profile.  */
            profile_offset = prog_unit->fb_hdr.fb_profile_offset
              + inline_func_hdr.func_hist_table_offset
              + sample.hist_offset * sizeof(struct fb_info_hist);
            if (fseek (infile, profile_offset, SEEK_SET) != 0)
              {
                error ("read_inline_function(): fseek profile_data error.");
                return curr_num_samples;
              }

            if (fread (hist_buf,
                       sample.num_value,
                       sizeof (struct fb_info_hist),
                       infile) != sizeof (struct fb_info_hist))
              {
                error ("read_inline_function(): fread profile_data error.");
                return curr_num_samples;
              }

            inline_sample_buf[j].values = (struct sample_hist *)
              xcalloc (sample.num_value, sizeof (struct sample_hist));

            for (k = 0; k < sample.num_value; k++) {
              inline_sample_buf[j].values[k].type = hist_buf[k].type;
              if (hist_buf[k].type == CALL_HIST)
                {
                  inline_sample_buf[j].values[k].value.func_name =
                      &(prog_unit->str_table[hist_buf[k].value]);
                  sp_add_indirect_call (
                      &(prog_unit->str_table[func_hdr->func_name_index]),
                      &(prog_unit->str_table[hist_buf[k].value]),
                      hist_buf[k].count);
                }
              else
                {
                  inline_sample_buf[j].values[k].value.value = hist_buf[k].value;
                }
              inline_sample_buf[j].values[k].count = hist_buf[k].count;
            }
          }

          /* All the entries share the inline_stack. Mark the first entry to
             track when to delete the inline_stack.  */
          if (j == 0)
            inline_sample_buf[j].is_first = true;
          else
            inline_sample_buf[j].is_first = false;

	  if (sample.freq > sp_max_count)
	    sp_max_count = sample.freq;

          /* Insert new sample into inline hash table.  */
          slot = (struct sample_inline_freq **)
              htab_find_slot (sp_inline_htab, &inline_sample_buf[j], INSERT);
          if (*slot)
            {
	      if (PARAM_VALUE (PARAM_SAMPLEFDO_USE_DISCRIMINATORS))
		{
		  inform (0, "Duplicate entry: %s:%d",
			  inline_sample_buf[j].filename, 
			  inline_sample_buf[j].line_num);
		}
	      else
		{
		  /* When not using discriminators, merge multiple
		     entries with different discriminator values */
		  (*slot)->freq += inline_sample_buf[j].freq;
		  (*slot)->num_instr += inline_sample_buf[j].num_instr;
		}
	    }
          else
            {
              *slot = &inline_sample_buf[j];
	      curr_num_samples++;
            }
	}
    }

    return curr_num_samples;
} 

/* Rountine that returns the total number of option string entries in the
   module specified by the header HDR.  */
static unsigned long long
sp_module_num_strings (const struct module_sample_hdr *hdr)
{
  return hdr->num_quote_paths +
         hdr->num_bracket_paths +
         hdr->num_cpp_defines +
         hdr->num_cpp_includes +
         hdr->num_cl_args;
}

/* Routine that reads in the option info (stored in PROFILE, and header HDR),
   and update the MODULE_INFO. Use PROG_UNIT to get the string table. If the
   module is primary module (as specified by IS_PRIMARY), set the flags
   accordingly.  */
static void
sp_add_module (struct gcov_module_info **module_info,
               struct fb_info_module *profile,
               struct module_sample_hdr *hdr,
               gcov_unsigned_t is_primary,
               struct profile *prog_unit)
{
  unsigned int i, current_offset = 0;
  size_t info_sz;
  info_sz = sizeof (struct gcov_module_info) +
            sizeof (void *) * sp_module_num_strings (hdr);

  *module_info = XCNEWVAR (struct gcov_module_info, info_sz);
  (*module_info)->ident = hdr->module_name_index;
  (*module_info)->is_primary = is_primary;
  (*module_info)->is_exported = is_primary ? hdr->exported : 1;
  (*module_info)->source_filename
      = &(prog_unit->str_table[hdr->module_name_index]);
  (*module_info)->num_quote_paths = hdr->num_quote_paths;
  (*module_info)->num_bracket_paths = hdr->num_bracket_paths;
  (*module_info)->num_cpp_defines = hdr->num_cpp_defines;
  (*module_info)->num_cpp_includes = hdr->num_cpp_includes;
  (*module_info)->num_cl_args = hdr->num_cl_args;
  /* The first part of the sp_module_info profile is the auxilary modules.
     We skip this section here because it will not be used in the
     module_infos.  */
  profile += hdr->num_aux_modules;

  for (i = 0; i < sp_module_num_strings (hdr); i++)
    (*module_info)->string_array[current_offset++]
        = &(prog_unit->str_table[(profile++)->string_offset]);

/* TODO: SampleFDO also need to add the support to check if the module contains
         ASM_STMT.  */
}

/* Routine that takes the module id ID as input. It traverse the module header
   table HDR from START to END, and returns the relative position of the
   profile in the feedback data file.  */
static int
sp_find_module_by_id (struct module_sample_hdr *hdr,
                      int start, int end, unsigned int id)
{
  int i;
  for (i = start; i < end; i++)
    {
      if (hdr[i].module_name_index == id)
        return i;
    }
  return -1;
}

/* Read in the module grouping information from the sample profile INFILE.
   Use PROG_UNIT to get the string table.  */
static void
sp_read_modules (FILE *infile, struct profile *prog_unit)
{
  struct fb_sample_hdr *fb_hdr = &(prog_unit->fb_hdr);
  unsigned long long module_start = fb_hdr->fb_module_hdr_offset;
  unsigned int num_module_hdr = fb_hdr->fb_num_module_hdr;
  unsigned int i;
  const char *curr_file_name;

  void *buf = xmalloc (fb_hdr->fb_module_profile_size);

  struct module_sample_hdr *hdr = (struct module_sample_hdr *) buf;

  if (fseek (infile, module_start, SEEK_SET) != 0)
    error ("read_inline_function(): fseek profile_data error.");
  if (fread (buf, 1, fb_hdr->fb_module_profile_size, infile) !=
      fb_hdr->fb_module_profile_size)
    error ("sp_read_modules(): fread module_hdr error.");

  curr_file_name = in_fnames[0];
  if (dump_file)
    fprintf (dump_file, "\nDoing Module grouping for %s.\n", curr_file_name);

  /* Read in the aux module info for the primary module.  */
  for (i = 0; i < num_module_hdr; i++)
    {
      char *file_name = &(prog_unit->str_table[hdr[i].module_name_index]);
      /* Traverse the modules to find the primarial module.  */
      if (!strcmp (realname (file_name), realname (curr_file_name)))
        {
          unsigned int j;
          int curr_module = 1, idx = 0;
          struct fb_info_module *modules =
            (struct fb_info_module *) (((char *)buf) +
            hdr[i].module_profile_offset);
          module_infos = XCNEWVEC (struct gcov_module_info *,
                                   (hdr[i].num_aux_modules + 1));
          sp_add_module (module_infos, modules, &hdr[i], true, prog_unit);
          primary_module_id = hdr[i].module_name_index;
          if (dump_file)
            fprintf (dump_file, "Aux Modules:\n");
          for (j = 0; j < hdr[i].num_aux_modules; j++, idx++)
            {
              struct fb_info_module *aux_modules;
              char *aux_name =
                  &(prog_unit->str_table[modules[j].string_offset]);
              if (primary_module_id == modules[j].string_offset)
                continue;
              idx = sp_find_module_by_id (hdr, idx, num_module_hdr,
                                          modules[j].string_offset);
              if (idx < 0)
                error ("sp_read_modules(): aux module %s doesn't exist.",
                       aux_name);

              aux_modules =
                  (struct fb_info_module *) (((char *)buf) +
                  hdr[idx].module_profile_offset);
              sp_add_module (&module_infos[curr_module++], aux_modules,
                             &hdr[idx], false, prog_unit);
              add_input_filename (aux_name);
              if (dump_file)
                fprintf (dump_file, "\t%s\n", aux_name);
            }
          /* Because we already found the primary module, and finished
             processing, we can stop traversing other modules.  */
          break;
        }
    }
}

/* Read sample profile file with filename IN_FILENAME to initialize sp_htab and
   PROG_UNIT. Return the number of <> tuples.  */
static unsigned long long
sp_reader (const char *in_filename, struct profile *prog_unit)
{
  unsigned int num_funcs;
  FILE *in_file;
  unsigned int i;
  unsigned long long j;
  unsigned long long num_lines;
  unsigned long long profile_offset;
  unsigned long long num_samples = 0;

  if ((in_file = fopen (in_filename, "r")) == NULL)
    {
      error ("Error opening sample profile file %s.\n", in_filename);
      return 0;
    }

  if (read_file_header (in_file, prog_unit) != 0)
    {
      error ("Error reading file header of %s.\n", in_filename);
      fclose (in_file);
      return 0;
    }

  if (read_string_table (in_file, prog_unit) != 0)
    {
      error ("Error reading string table of %s.\n", in_filename);
      if (prog_unit->str_table)
	free (prog_unit->str_table);
      fclose (in_file);
      return 0;
    }

  if (flag_dyn_ipa)
    sp_read_modules (in_file, prog_unit);

  num_funcs = prog_unit->fb_hdr.fb_func_hdr_num;
  for (i = 0; i < num_funcs; ++i)
    {
      struct func_sample_hdr func_hdr;
      struct sample_freq_detail **slot;

      if (read_function_header (in_file, i, prog_unit, &func_hdr) != 0)
	{
	  error ("Error reading the %dth function header of %s.\n", i,
		  in_filename);
	  if (prog_unit->str_table)
	    free (prog_unit->str_table);
	  fclose (in_file);
	  return 0;
	}

      num_lines = func_hdr.func_num_freq_entries;

      sample_buf = (struct sample_freq_detail *)
              xcalloc (num_lines + 1, sizeof (struct sample_freq_detail));

      sample_buf[0].func_name =
          &(prog_unit->str_table[func_hdr.func_name_index]);
      sample_buf[0].filename =
          &(prog_unit->str_table[func_hdr.func_name_index]);
      sample_buf[0].line_num = 0;
      sample_buf[0].discriminator = 0;
      sample_buf[0].freq = func_hdr.entry_count;
      sample_buf[0].num_instr = 0;
      slot = (struct sample_freq_detail **)
              htab_find_slot (sp_htab, &sample_buf[0], INSERT);
      if (!*slot) {
        *slot = &sample_buf[0];
      }

      for (j = 1; j <= num_lines; ++j)
	{
	  struct fb_info_freq sample;
          /* Get the offset of the frequency profile.  */
          profile_offset = prog_unit->fb_hdr.fb_profile_offset +
                           func_hdr.func_profile_offset +
                           func_hdr.func_freq_offset + /* This should be 0 */
                           (j - 1) * sizeof (sample);
          if (fseek (in_file, profile_offset, SEEK_SET) != 0)
            return 0;
	  if (fread (&sample, 1, sizeof (sample), in_file) != sizeof (sample))
	    return 0;

          sample_buf[j].func_name = 
              &(prog_unit->str_table[func_hdr.func_name_index]);
	  sample_buf[j].filename =
  	      &(prog_unit->str_table[sample.filename_offset]);
	  sample_buf[j].line_num = sample.line_num;
	  sample_buf[j].discriminator = DISCRIM (sample.discriminator);
	  sample_buf[j].freq = sample.freq;
          sample_buf[j].num_instr = sample.num_instr;
	  if (sample.freq > sp_max_count)
	    sp_max_count = sample.freq;

          sample_buf[j].num_value = sample.num_value;
          if (sample.num_value > 0) {
            unsigned long long k;
            struct fb_info_hist *hist_buf = (struct fb_info_hist *)
                alloca (sample.num_value * sizeof (struct fb_info_hist));

            /* Get the offset of the value profile.  */
            profile_offset = prog_unit->fb_hdr.fb_profile_offset
              + func_hdr.func_hist_table_offset
              + sample.hist_offset * sizeof (struct fb_info_hist);
            if (fseek (in_file, profile_offset, SEEK_SET) != 0)
              return 0;

            if (fread (hist_buf,
                       sample.num_value,
                       sizeof (struct fb_info_hist),
                       in_file) != sizeof (struct fb_info_hist)) {
              return 0;
            }
            sample_buf[j].values = (struct sample_hist *)
              xcalloc (sample.num_value, sizeof (struct sample_hist));

            for (k = 0; k < sample.num_value; k++) {
              sample_buf[j].values[k].type = hist_buf[k].type;
              if (hist_buf[k].type == CALL_HIST)
                {
                  sample_buf[j].values[k].value.func_name =
                      &(prog_unit->str_table[hist_buf[k].value]);
                  sp_add_indirect_call (
                      &(prog_unit->str_table[func_hdr.func_name_index]),
                      &(prog_unit->str_table[hist_buf[k].value]),
                      hist_buf[k].count);
                }
              else
                {
                  sample_buf[j].values[k].value.value = hist_buf[k].value;
                }
              sample_buf[j].values[k].count = hist_buf[k].count;
            }
          }

          /* Insert new sample into hash table.  */
          slot = (struct sample_freq_detail **)
              htab_find_slot (sp_htab, &sample_buf[j], INSERT);
          if (*slot)
            {
	      if (PARAM_VALUE (PARAM_SAMPLEFDO_USE_DISCRIMINATORS))
		{
		  char *func_name =
		    &(prog_unit->str_table[func_hdr.func_name_index]);
		  inform (0, "Duplicate entry: %s:%d func_name:%s",
			  sample_buf[j].filename,
			  sample_buf[j].line_num, func_name);
		}
	      else
		{
		  /* When not using discriminators, merge multiple
		     entries with different discriminator values */
		  (*slot)->freq += sample_buf[j].freq;
		  (*slot)->num_instr += sample_buf[j].num_instr;
		}
            }
          else
            {
              *slot = &sample_buf[j];
	      num_samples++;
            }
	}
        if (func_hdr.func_num_inline_entries > 0)
          num_samples = read_inline_function (in_file, prog_unit, &func_hdr,
                                              num_samples);
    }

  fclose (in_file);
  return num_samples;
}

static int
compare (const void *a, const void *b) {
  const struct sample_hist *x = (const struct sample_hist *) a;
  const struct sample_hist *y = (const struct sample_hist *) b;
  if (x->type != y->type)
    {
      return y->type - x->type;
    }
  else if (x->count != y->count)
    {
      return y->count - x->count;
    }
  else
    {
      if (x->type == CALL_HIST)
        return strcmp (x->value.func_name, y->value.func_name);
      else
        return y->value.value - x->value.value;
    }
}

/* Compute the BB execution count from the sample profile data.  */
void
sp_annotate_bb (basic_block bb)
{
  gimple_stmt_iterator si;
  /* The number of IRs in a BB.  */
  int num_ir = 0, num_instr_sampled = 0;
  gcov_type sum_ir_count = 0;
  gcov_type bb_max_count = 0;
  int lineno, discriminator;
  struct expanded_inline_location inline_stack[FB_INLINE_MAX_STACK];
  int inline_stack_depth;
  int num_lines = 0, num_inlines = 0;
  void *lines[MAX_LINES_PER_BASIC_BLOCK];
  void *lines_inline[MAX_LINES_PER_BASIC_BLOCK];

  if (flag_sample_profile_use_entry && bb == ENTRY_BLOCK_PTR)
    {
      struct sample_freq_detail ir_loc;
      struct sample_freq_detail **slot;
      struct sample_freq_detail *htab_entry = NULL;
      ir_loc.filename
            = sp_get_real_funcname (current_function_assembler_name ());
      ir_loc.func_name
            = sp_get_real_funcname (current_function_assembler_name ());
      ir_loc.line_num = 0;
      ir_loc.discriminator = 0;

      slot = (struct sample_freq_detail **)
        htab_find_slot (sp_htab, &ir_loc, INSERT);
      if (*slot) {
        htab_entry = *slot;
      }

      if (htab_entry) {
        bb->count = htab_entry->freq;
        bb->confidence = HIGH_CONFIDENCE;
        if (dump_file)
          fprintf (dump_file,
                   "BB%d: average_count=" HOST_WIDEST_INT_PRINT_DEC ", ",
                   bb->index, bb->count);
        return;
      }
    }

  for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
    {
      hashval_t hash_val;
      int i;
      gimple stmt = gsi_stmt (si);
      lineno = get_lineno (stmt);
      if (lineno == -1)
	continue;
      discriminator = DISCRIM (get_discriminator (stmt));

      inline_stack_depth = sp_get_inline_stack (stmt, inline_stack);
      gcc_assert (inline_stack_depth < FB_INLINE_MAX_STACK);

      if (inline_stack_depth > 0)
        {
          /* Look in inline hash table for matching entry.  */
          struct sample_inline_freq inline_loc;
          struct sample_inline_freq *inline_htab_entry;

          inline_loc.depth = inline_stack_depth;
          inline_loc.inline_stack = inline_stack;
          inline_loc.func_name
            = sp_get_real_funcname (current_function_assembler_name ());
          inline_loc.filename = gimple_filename (stmt);
          inline_loc.line_num = lineno;
	  inline_loc.discriminator = discriminator;

          inline_htab_entry = (struct sample_inline_freq *)
              htab_find (sp_inline_htab, (void *) &inline_loc);

          if (!inline_htab_entry)
            continue;

          num_ir++;

          if (flag_value_profile_transformations
              && inline_htab_entry->num_value > 0)
            {
              qsort (inline_htab_entry->values,
                     inline_htab_entry->num_value,
                     sizeof(struct sample_hist),
                     compare);
              gimple_sample_vpt (stmt,
                                 inline_htab_entry->values,
                                 inline_htab_entry->num_value);
            }

          for (i = num_inlines - 1; i >= 0; i--)
            if ((void *) inline_htab_entry == lines_inline[i])
              break;
          if (i >= 0)
            continue;
          gcc_assert (num_inlines < MAX_LINES_PER_BASIC_BLOCK);
          lines_inline[num_inlines++] = (void *) inline_htab_entry;

          sum_ir_count += inline_htab_entry->freq;
          num_instr_sampled += inline_htab_entry->num_instr;
      
          if (bb_max_count <  inline_htab_entry->freq)
	    bb_max_count = inline_htab_entry->freq;

          if (dump_file)
            fprintf (dump_file,
	             "BB%d: %s line_%d (" HOST_WIDEST_INT_PRINT_DEC ")\n",
	             bb->index, inline_loc.filename, lineno,
                     (HOST_WIDEST_INT) inline_htab_entry->freq);
        }
      else
        {
          /* Not an inlined location. Look in regular hash table.  */
          struct sample_freq_detail ir_loc;
          struct sample_freq_detail *htab_entry;
          ir_loc.filename = gimple_filename (stmt);
          ir_loc.func_name
            = sp_get_real_funcname (current_function_assembler_name ());
          ir_loc.line_num = lineno;
	  ir_loc.discriminator = discriminator;

          hash_val = create_hash_string (ir_loc.filename, lineno,
                                         discriminator);

          htab_entry = (struct sample_freq_detail *)
          htab_find_with_hash (sp_htab, (void *) &ir_loc, hash_val);

          if (!htab_entry)
            continue;

          num_ir++;

          if (flag_value_profile_transformations && htab_entry->num_value > 0)
            {
              qsort (htab_entry->values,
                     htab_entry->num_value,
                     sizeof(struct sample_hist),
                     compare);
              gimple_sample_vpt (stmt,
                                 htab_entry->values,
                                 htab_entry->num_value);
            }


          for (i = num_lines - 1; i >= 0; i--)
            if ((void *) htab_entry == lines[i])
              break;
          if (i >= 0)
            continue;
          gcc_assert (num_lines < MAX_LINES_PER_BASIC_BLOCK);
          lines[num_lines++] = (void *) htab_entry;

          sum_ir_count += htab_entry->freq;
          num_instr_sampled += htab_entry->num_instr;
          if (bb_max_count <  htab_entry->freq)
	    bb_max_count = htab_entry->freq;

          if (dump_file)
            fprintf (dump_file,
	             "BB%d: %s line_%d (" HOST_WIDEST_INT_PRINT_DEC ")\n",
		     bb->index, ir_loc.filename, lineno,
                     (HOST_WIDEST_INT) htab_entry->freq);
        }
    }

  if (num_instr_sampled > 0)
    {
      if (flag_sample_profile_aggregate_using
          == SAMPLE_PROFILE_AGGREGATE_USING_MAX)
	bb->count = bb_max_count;
      else if (flag_sample_profile_aggregate_using
               == SAMPLE_PROFILE_AGGREGATE_USING_AVG)
	bb->count = sum_ir_count / num_instr_sampled;
      else
	gcc_unreachable();
      /* If there are many statements in a BB, but no instructions
         were sampled, one can be confident in the sampled profile
         count. */
      if (bb->count == 0
          && num_ir > PARAM_VALUE (PARAM_SAMPLEFDO_LARGE_BLOCK_THRESH)
          && num_instr_sampled > PARAM_VALUE (PARAM_SAMPLEFDO_INST_THRESH))
        bb->confidence = HIGH_CONFIDENCE;
      else
        bb->confidence = NORMAL_CONFIDENCE;
    }
  else
    {
      bb->count = 0;
      bb->confidence = LOW_CONFIDENCE;
    }

  if (dump_file)
    {
      fprintf (dump_file,
	       "BB%d: average_count=" HOST_WIDEST_INT_PRINT_DEC ", ",
	       bb->index, bb->count);
      fprintf (dump_file, "maximal_count=" HOST_WIDEST_INT_PRINT_DEC ". ",
	       bb_max_count);
      fprintf (dump_file, "num_ir=%u, num_instr_sampled=%u.\n", num_ir,
	       num_instr_sampled);
    }

}

/* Initialize edge counts and edge probabilities (e->count,
   e->probability) with sample count data.  */
static void
sp_init_cfg (void)
{
  basic_block bb;
  edge e;
  edge_iterator ei;


  FOR_BB_BETWEEN (bb, ENTRY_BLOCK_PTR, EXIT_BLOCK_PTR, next_bb)
    {
      gcov_type total_count = 0;
      int num_edge = 0;
      FOR_EACH_EDGE (e, ei, bb->succs)
	{
	  total_count += e->dest->count;
	  num_edge++;
	}

      if (total_count == 0)
	{
	  /* If none of the successor blocks have samples, divide
	     the source block's weight evenly among the out
	     edges. */
	  
	  FOR_EACH_EDGE (e, ei, bb->succs)
	    {
	      e->count = e->src->count / num_edge;
	      e->probability = REG_BR_PROB_BASE / num_edge;
	    }
	}
      else
	{
	  /* Compute edge probabilities using the source and dest
	     basic block counts.  This computation is wrong for
	     critical edges, but we rely on MCF to clean up these
	     inaccuracies. */

	  FOR_EACH_EDGE (e, ei, bb->succs)
	    {
	      e->count = e->src->count * e->dest->count / total_count;
	      e->probability = REG_BR_PROB_BASE * e->dest->count / total_count;
	    }
	}
    }

  /* Initialize ENTRY and EXIT counts.  */
  if (!flag_sample_profile_use_entry)
    {
      FOR_EACH_EDGE (e, ei, ENTRY_BLOCK_PTR->succs)
        {
          ENTRY_BLOCK_PTR->count += e->count;
        }
    }

  FOR_EACH_EDGE (e, ei, EXIT_BLOCK_PTR->preds)
    {
      EXIT_BLOCK_PTR->count += e->count;
    }
}

/* Adjust the BB and edge frequency.  */
void
sp_smooth_cfg (void)
{
  compact_blocks ();
  sp_init_cfg ();
  add_noreturn_fake_exit_edges ();
  mcf_smooth_cfg ();
  remove_fake_exit_edges ();
  counts_to_freqs ();
}

/* Set the global variables to mark that the profile is availabe for the
   function. Also set the the sum_max to MAX_COUNT.  */
void
sp_set_sample_profile (gcov_type max_count)
{
  if (!profile_info || profile_status != PROFILE_READ)
    {
      profile_status = PROFILE_READ;
      sp_profile_info->runs = 1;
      sp_profile_info->sum_max = 0;
      profile_info = sp_profile_info;
    }
  if (max_count > profile_info->sum_max)
    sp_profile_info->sum_max = max_count;
}

/* Annotate CFG with sample profile. Sets basic block and edge counts and
   profile_info using sample profile input. The basic block and edge counts
   are "smoothed" to be flow-consistent using a Minimum-Cost Flow algorithm.  */
static void
sp_annotate_cfg (void)
{
  basic_block bb;
  int num_bb_annotated = 0;
  gcov_type func_max_count = 0;
  cgraph_need_artificial_indirect_call_edges = 0;

  if (dump_file)
    {
      fprintf (dump_file,
	       "\nAnnotate CFG for function %s() in file %s with sample profile.\n",
	       lang_hooks.decl_printable_name (current_function_decl, 2),
	       main_input_filename);
      fprintf (dump_file, "n_basic_blocks=%d, n_edges=%d.\n\n",
	       n_basic_blocks, n_edges);
      fprintf (dump_file, "\nStatistics for sp_htab:\n");
      print_hash_table_statistics (sp_htab);
      fprintf (dump_file, "\nStatistics for sp_inline_htab:\n");
      print_hash_table_statistics (sp_inline_htab);
    }

  /* Annotate basic blocks with sample data.  */
  FOR_ALL_BB (bb)
  {
    sp_annotate_bb (bb);
    if (bb->count)
      {
	num_bb_annotated++;
	if (bb->count > func_max_count)
	  func_max_count = bb->count;
      }
  }

  if (dump_file)
    {
      fprintf (dump_file, "\n%d of %d BBs are sampled. ", num_bb_annotated,
	       n_basic_blocks - 2);
      fprintf (dump_file, "func_max_count=" HOST_WIDEST_INT_PRINT_DEC ", ",
	       func_max_count);
      fprintf (dump_file, "sp_max_count=" HOST_WIDEST_INT_PRINT_DEC ".\n",
	       sp_max_count);
    }

  if (num_bb_annotated > 1
      || (num_bb_annotated == 1 && (n_basic_blocks < MIN_SAMPLE_BB_COUNT)))
    {
      sp_smooth_cfg ();
      sp_set_sample_profile (sp_max_count);
      if (flag_value_profile_transformations)
        {
          gimple_register_value_prof_hooks();
          value_profile_transformations ();
        }
    }
  else
    {
      FOR_EACH_BB (bb)
        bb->count = 0;
    }
}

/* Read sample file to initialize sp_htab. Called in toplev.c.
   This function works in the file-level instead of function-level.
   This can save time.  */
void
init_sample_profile (void)
{
  if (flag_branch_probabilities)
    {
      inform
	(0, "Cannot set both -fbranch-probabilities and -fsample-profile. "
         "Disable -fsample-profile now.");
      flag_sample_profile = 0;
      return;
    }

  if (sample_data_name == NULL)
    sample_data_name = DEFAULT_SAMPLE_DATAFILE;

  sp_htab = htab_create_alloc ((size_t) SP_HTAB_INIT_SIZE,
                               sp_info_hash,
                               sp_info_eq,
                               sp_info_del,
                               xcalloc,
                               free);

  sp_inline_htab = htab_create_alloc ((size_t) SP_INLINE_HTAB_INIT_SIZE,
                                      sp_inline_info_hash,
                                      sp_inline_info_eq,
                                      sp_inline_info_del,
                                      xcalloc,
                                      free);

  if (flag_dyn_ipa)
    sp_funcname_htab = htab_create_alloc ((size_t) SP_FUNCNAME_HTAB_INIT_SIZE,
                                          sp_funcname_hash,
                                          sp_funcname_eq,
                                          0,
                                          xcalloc,
                                          free);
  sp_indirect_htab = htab_create_alloc ((size_t) SP_FUNCNAME_HTAB_INIT_SIZE,
                                        sp_indirect_hash,
                                        sp_indirect_eq,
                                        0,
                                        xcalloc,
                                        free);

  sp_num_samples = sp_reader (sample_data_name, &prog_unit);
  sp_profile_info =
    (struct gcov_ctr_summary *) xcalloc (1, sizeof (struct gcov_ctr_summary));

  if (!sp_num_samples)
    {
      inform
	(0, "No available data in the sample file %s. "
         "Disable -fsample-profile now.",
	 sample_data_name);
      flag_sample_profile = 0;
    }
  else
    inform (0, "There are %llu samples in file %s", sp_num_samples,
	    sample_data_name);
}

/* Finalize some data structures. Called in toplev.c.  */
void
end_sample_profile (void)
{
  if (prog_unit.str_table)
    free (prog_unit.str_table);
  if (sp_htab)
    htab_delete (sp_htab);
  sp_htab = NULL;
  free (sample_buf);
  if (sp_inline_htab)
    htab_delete (sp_inline_htab);
  sp_inline_htab = NULL;
  if (sp_indirect_htab)
    htab_delete (sp_indirect_htab);
  free (inline_sample_buf);
  if (sp_profile_info)
    free (sp_profile_info);
}

/* Main entry of sample_profile pass.  */
static unsigned int
execute_sample_profile (void)
{
  /* Annotate CFG with sample profile.  */
  flow_call_edges_add (NULL);
  compact_blocks ();
  remove_fake_edges ();
  sp_annotate_cfg ();
  cfun->after_tree_profile = 1;
  return 0;
}

static bool
gate_sample_profile (void)
{
  /* This is a redundant check. Just for safety.  */
  gcc_assert (!(flag_sample_profile && flag_branch_probabilities));
  return flag_sample_profile;
}

struct gimple_opt_pass pass_tree_sample_profile = {
  {
    GIMPLE_PASS,
    "sample_profile",
    gate_sample_profile,
    execute_sample_profile,
    NULL,
    NULL,
    0,
    TV_TREE_SAMPLE,
    PROP_cfg,
    0,
    0,
    0,
    TODO_dump_func,
  }
};


/* Entry for profile_dump pass.  */
static unsigned int
execute_profile_dump (void)
{
  char *dump_cfg_filename = NULL;
  if (flag_branch_probabilities)
    {
      /* Dump edge profile.  */
      dump_cfg_filename = concat(dump_base_name, ".prof.compare.branch", NULL);
    }
  else if (flag_sample_profile)
    {
      /* Dump sample profile.  */
      dump_cfg_filename = concat(dump_base_name, ".prof.compare.sample", NULL);
    }

  if (dump_cfg_filename)
    {
      dump_cfg_profile (dump_cfg_filename);
      free (dump_cfg_filename);
    }
  return 0;
}

static bool
gate_profile_dump (void)
{
  return (flag_profile_dump
	  && (flag_sample_profile || flag_branch_probabilities));
}

struct gimple_opt_pass pass_tree_profile_dump = {
  {
    GIMPLE_PASS,
    "profile_dump",
    gate_profile_dump,
    execute_profile_dump,
    NULL,
    NULL,
    0,
    0,
    PROP_cfg,
    0,
    0,
    0,
    0
  }
};
