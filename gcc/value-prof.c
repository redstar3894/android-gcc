/* Transformations based on profile information for values.
   Copyright (C) 2003, 2004, 2005, 2006, 2007, 2008, 2009  Free Software
   Foundation, Inc.

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

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "rtl.h"
#include "expr.h"
#include "hard-reg-set.h"
#include "basic-block.h"
#include "value-prof.h"
#include "output.h"
#include "flags.h"
#include "insn-config.h"
#include "recog.h"
#include "optabs.h"
#include "regs.h"
#include "ggc.h"
#include "tree-flow.h"
#include "tree-flow-inline.h"
#include "tree-inline.h"
#include "diagnostic.h"
#include "coverage.h"
#include "tree.h"
#include "gcov-io.h"
#include "cgraph.h"
#include "timevar.h"
#include "tree-pass.h"
#include "toplev.h"
#include "pointer-set.h"
#include "langhooks.h"
#include "params.h"
#include "tree-sample-profile.h"

/* TODO(martint): Switch from math.h to mpfr.h. */
#include <math.h>

static struct value_prof_hooks *value_prof_hooks;

/* In this file value profile based optimizations are placed.  Currently the
   following optimizations are implemented (for more detailed descriptions
   see comments at value_profile_transformations):

   1) Division/modulo specialization.  Provided that we can determine that the
      operands of the division have some special properties, we may use it to
      produce more effective code.
   2) Speculative prefetching.  If we are able to determine that the difference
      between addresses accessed by a memory reference is usually constant, we
      may add the prefetch instructions.
      FIXME: This transformation was removed together with RTL based value
      profiling.

   3) Indirect/virtual call specialization. If we can determine most
      common function callee in indirect/virtual call. We can use this
      information to improve code effectiveness (especially info for
      inliner).

   Every such optimization should add its requirements for profiled values to
   insn_values_to_profile function.  This function is called from branch_prob
   in profile.c and the requested values are instrumented by it in the first
   compilation with -fprofile-arcs.  The optimization may then read the
   gathered data in the second compilation with -fbranch-probabilities.

   The measured data is pointed to from the histograms
   field of the statement annotation of the instrumented insns.  It is
   kept as a linked list of struct histogram_value_t's, which contain the
   same information as above.  */


static tree gimple_divmod_fixed_value (gimple, tree, int, gcov_type, gcov_type);
static tree gimple_mod_pow2 (gimple, int, gcov_type, gcov_type);
static tree gimple_mod_subtract (gimple, int, int, int, gcov_type, gcov_type,
				 gcov_type);
static bool gimple_float_math_call_transform (gimple_stmt_iterator *);
static bool gimple_divmod_fixed_value_transform (gimple_stmt_iterator *);
static bool gimple_mod_pow2_value_transform (gimple_stmt_iterator *);
static bool gimple_mod_subtract_transform (gimple_stmt_iterator *);
static bool gimple_stringops_transform (gimple_stmt_iterator *);
static bool gimple_ic_transform (gimple);

/* Allocate histogram value.  */

static histogram_value
gimple_alloc_histogram_value (struct function *fun ATTRIBUTE_UNUSED,
			      enum hist_type type, gimple stmt, tree value)
{
   histogram_value hist = (histogram_value) xcalloc (1, sizeof (*hist));
   hist->hvalue.value = value;
   hist->hvalue.stmt = stmt;
   hist->type = type;
   return hist;
}

/* Hash value for histogram.  */

static hashval_t
histogram_hash (const void *x)
{
  return htab_hash_pointer (((const_histogram_value)x)->hvalue.stmt);
}

/* Return nonzero if decl_id of die_struct X is the same as UID of decl *Y.  */

static int
histogram_eq (const void *x, const void *y)
{
  return ((const_histogram_value) x)->hvalue.stmt == (const_gimple) y;
}

/* Set histogram for STMT.  */

static void
set_histogram_value (struct function *fun, gimple stmt, histogram_value hist)
{
  void **loc;
  if (!hist && !VALUE_HISTOGRAMS (fun))
    return;
  if (!VALUE_HISTOGRAMS (fun))
    VALUE_HISTOGRAMS (fun) = htab_create (1, histogram_hash,
				           histogram_eq, NULL);
  loc = htab_find_slot_with_hash (VALUE_HISTOGRAMS (fun), stmt,
                                  htab_hash_pointer (stmt),
				  hist ? INSERT : NO_INSERT);
  if (!hist)
    {
      if (loc)
	htab_clear_slot (VALUE_HISTOGRAMS (fun), loc);
      return;
    }
  *loc = hist;
}

/* Get histogram list for STMT.  */

histogram_value
gimple_histogram_value (struct function *fun, gimple stmt)
{
  if (!VALUE_HISTOGRAMS (fun))
    return NULL;
  return (histogram_value) htab_find_with_hash (VALUE_HISTOGRAMS (fun), stmt,
						htab_hash_pointer (stmt));
}

/* Add histogram for STMT.  */

void
gimple_add_histogram_value (struct function *fun, gimple stmt,
			    histogram_value hist)
{
  hist->hvalue.next = gimple_histogram_value (fun, stmt);
  set_histogram_value (fun, stmt, hist);
}


/* Remove histogram HIST from STMT's histogram list.  */

void
gimple_remove_histogram_value (struct function *fun, gimple stmt,
			       histogram_value hist)
{
  histogram_value hist2 = gimple_histogram_value (fun, stmt);
  if (hist == hist2)
    {
      set_histogram_value (fun, stmt, hist->hvalue.next);
    }
  else
    {
      while (hist2->hvalue.next != hist)
	hist2 = hist2->hvalue.next;
      hist2->hvalue.next = hist->hvalue.next;
    }
  free (hist->hvalue.counters);
#ifdef ENABLE_CHECKING
  memset (hist, 0xab, sizeof (*hist));
#endif
  free (hist);
}


/* Lookup histogram of type TYPE in the STMT.  */

histogram_value
gimple_histogram_value_of_type (struct function *fun, gimple stmt,
				enum hist_type type)
{
  histogram_value hist;
  for (hist = gimple_histogram_value (fun, stmt); hist;
       hist = hist->hvalue.next)
    if (hist->type == type)
      return hist;
  return NULL;
}

/* Dump information about HIST to DUMP_FILE.  */

static void
dump_histogram_value (FILE *dump_file, histogram_value hist)
{
  switch (hist->type)
    {
    case HIST_TYPE_INTERVAL:
      fprintf (dump_file, "Interval counter range %d -- %d",
	       hist->hdata.intvl.int_start,
	       (hist->hdata.intvl.int_start
	        + hist->hdata.intvl.steps - 1));
      if (hist->hvalue.counters)
	{
	   unsigned int i;
	   fprintf(dump_file, " [");
           for (i = 0; i < hist->hdata.intvl.steps; i++)
	     fprintf (dump_file, " %d:"HOST_WIDEST_INT_PRINT_DEC,
		      hist->hdata.intvl.int_start + i,
		      (HOST_WIDEST_INT) hist->hvalue.counters[i]);
	   fprintf (dump_file, " ] outside range:"HOST_WIDEST_INT_PRINT_DEC,
		    (HOST_WIDEST_INT) hist->hvalue.counters[i]);
	}
      fprintf (dump_file, ".\n");
      break;

    case HIST_TYPE_POW2:
      fprintf (dump_file, "Pow2 counter ");
      if (hist->hvalue.counters)
	{
	   fprintf (dump_file, "pow2:"HOST_WIDEST_INT_PRINT_DEC
		    " nonpow2:"HOST_WIDEST_INT_PRINT_DEC,
		    (HOST_WIDEST_INT) hist->hvalue.counters[0],
		    (HOST_WIDEST_INT) hist->hvalue.counters[1]);
	}
      fprintf (dump_file, ".\n");
      break;

    case HIST_TYPE_SINGLE_VALUE:
      fprintf (dump_file, "Single value ");
      if (hist->hvalue.counters)
	{
	   fprintf (dump_file, "value:"HOST_WIDEST_INT_PRINT_DEC
		    " match:"HOST_WIDEST_INT_PRINT_DEC
		    " wrong:"HOST_WIDEST_INT_PRINT_DEC,
		    (HOST_WIDEST_INT) hist->hvalue.counters[0],
		    (HOST_WIDEST_INT) hist->hvalue.counters[1],
		    (HOST_WIDEST_INT) hist->hvalue.counters[2]);
	}
      fprintf (dump_file, ".\n");
      break;
    case HIST_TYPE_SINGLE_FLOAT_VALUE:
      fprintf (dump_file, "Single float value ");
      if (hist->hvalue.counters)
        {
           fprintf (dump_file, "value:%f"
        	    " match:"HOST_WIDEST_INT_PRINT_DEC
        	    " wrong:"HOST_WIDEST_INT_PRINT_DEC,
        	    gcov_type_to_float (hist->hvalue.counters[0]),
        	    (HOST_WIDEST_INT) hist->hvalue.counters[1],
        	    (HOST_WIDEST_INT) hist->hvalue.counters[2]);
        }
      fprintf (dump_file, ".\n");
      break;


    case HIST_TYPE_AVERAGE:
      fprintf (dump_file, "Average value ");
      if (hist->hvalue.counters)
	{
	   fprintf (dump_file, "sum:"HOST_WIDEST_INT_PRINT_DEC
		    " times:"HOST_WIDEST_INT_PRINT_DEC,
		    (HOST_WIDEST_INT) hist->hvalue.counters[0],
		    (HOST_WIDEST_INT) hist->hvalue.counters[1]);
	}
      fprintf (dump_file, ".\n");
      break;

    case HIST_TYPE_IOR:
      fprintf (dump_file, "IOR value ");
      if (hist->hvalue.counters)
	{
	   fprintf (dump_file, "ior:"HOST_WIDEST_INT_PRINT_DEC,
		    (HOST_WIDEST_INT) hist->hvalue.counters[0]);
	}
      fprintf (dump_file, ".\n");
      break;

    case HIST_TYPE_CONST_DELTA:
      fprintf (dump_file, "Constant delta ");
      if (hist->hvalue.counters)
	{
	   fprintf (dump_file, "value:"HOST_WIDEST_INT_PRINT_DEC
		    " match:"HOST_WIDEST_INT_PRINT_DEC
		    " wrong:"HOST_WIDEST_INT_PRINT_DEC,
		    (HOST_WIDEST_INT) hist->hvalue.counters[0],
		    (HOST_WIDEST_INT) hist->hvalue.counters[1],
		    (HOST_WIDEST_INT) hist->hvalue.counters[2]);
	}
      fprintf (dump_file, ".\n");
      break;
    case HIST_TYPE_INDIR_CALL:
      fprintf (dump_file, "Indirect call ");
      if (hist->hvalue.counters)
	{
	   fprintf (dump_file, "value:"HOST_WIDEST_INT_PRINT_DEC
		    " match:"HOST_WIDEST_INT_PRINT_DEC
		    " all:"HOST_WIDEST_INT_PRINT_DEC,
		    (HOST_WIDEST_INT) hist->hvalue.counters[0],
		    (HOST_WIDEST_INT) hist->hvalue.counters[1],
		    (HOST_WIDEST_INT) hist->hvalue.counters[2]);
	}
      fprintf (dump_file, ".\n");
      break;
    case HIST_TYPE_INDIR_CALL_TOPN:
      fprintf (dump_file, "Indirect call -- top N\n");
      /* TODO add more elaborate dumping code.  */
      break;
   }
}

/* Dump all histograms attached to STMT to DUMP_FILE.  */

void
dump_histograms_for_stmt (struct function *fun, FILE *dump_file, gimple stmt)
{
  histogram_value hist;
  for (hist = gimple_histogram_value (fun, stmt); hist; hist = hist->hvalue.next)
   dump_histogram_value (dump_file, hist);
}

/* Remove all histograms associated with STMT.  */

void
gimple_remove_stmt_histograms (struct function *fun, gimple stmt)
{
  histogram_value val;
  while ((val = gimple_histogram_value (fun, stmt)) != NULL)
    gimple_remove_histogram_value (fun, stmt, val);
}

/* Duplicate all histograms associates with OSTMT to STMT.  */

void
gimple_duplicate_stmt_histograms (struct function *fun, gimple stmt,
				  struct function *ofun, gimple ostmt)
{
  histogram_value val;
  for (val = gimple_histogram_value (ofun, ostmt); val != NULL; val = val->hvalue.next)
    {
      histogram_value new_val = gimple_alloc_histogram_value (fun, val->type, NULL, NULL);
      memcpy (new_val, val, sizeof (*val));
      new_val->hvalue.stmt = stmt;
      new_val->hvalue.counters = XNEWVAR (gcov_type, sizeof (*new_val->hvalue.counters) * new_val->n_counters);
      memcpy (new_val->hvalue.counters, val->hvalue.counters, sizeof (*new_val->hvalue.counters) * new_val->n_counters);
      gimple_add_histogram_value (fun, stmt, new_val);
    }
}


/* Move all histograms associated with OSTMT to STMT.  */

void
gimple_move_stmt_histograms (struct function *fun, gimple stmt, gimple ostmt)
{
  histogram_value val = gimple_histogram_value (fun, ostmt);
  if (val)
    {
      /* The following three statements can't be reordered,
         because histogram hashtab relies on stmt field value
	 for finding the exact slot. */
      set_histogram_value (fun, ostmt, NULL);
      for (; val != NULL; val = val->hvalue.next)
	val->hvalue.stmt = stmt;
      set_histogram_value (fun, stmt, val);
    }
}

static bool error_found = false;

/* Helper function for verify_histograms.  For each histogram reachable via htab
   walk verify that it was reached via statement walk.  */

static int
visit_hist (void **slot, void *data)
{
  struct pointer_set_t *visited = (struct pointer_set_t *) data;
  histogram_value hist = *(histogram_value *) slot;
  if (!pointer_set_contains (visited, hist))
    {
      error ("Dead histogram");
      dump_histogram_value (stderr, hist);
      debug_gimple_stmt (hist->hvalue.stmt);
      error_found = true;
    }
  return 1;
}


/* Verify sanity of the histograms.  */

void
verify_histograms (void)
{
  basic_block bb;
  gimple_stmt_iterator gsi;
  histogram_value hist;
  struct pointer_set_t *visited_hists;

  error_found = false;
  visited_hists = pointer_set_create ();
  FOR_EACH_BB (bb)
    for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
      {
	gimple stmt = gsi_stmt (gsi);

	for (hist = gimple_histogram_value (cfun, stmt); hist;
	     hist = hist->hvalue.next)
	  {
	    if (hist->hvalue.stmt != stmt)
	      {
		error ("Histogram value statement does not correspond to "
		       "the statement it is associated with");
		debug_gimple_stmt (stmt);
		dump_histogram_value (stderr, hist);
		error_found = true;
	      }
            pointer_set_insert (visited_hists, hist);
	  }
      }
  if (VALUE_HISTOGRAMS (cfun))
    htab_traverse (VALUE_HISTOGRAMS (cfun), visit_hist, visited_hists);
  pointer_set_destroy (visited_hists);
  if (error_found)
    internal_error ("verify_histograms failed");
}

/* Helper function for verify_histograms.  For each histogram reachable via htab
   walk verify that it was reached via statement walk.  */

static int
free_hist (void **slot, void *data ATTRIBUTE_UNUSED)
{
  histogram_value hist = *(histogram_value *) slot;
  free (hist->hvalue.counters);
#ifdef ENABLE_CHECKING
  memset (hist, 0xab, sizeof (*hist));
#endif
  free (hist);
  return 1;
}

void
free_histograms (void)
{
  if (VALUE_HISTOGRAMS (cfun))
    {
      htab_traverse (VALUE_HISTOGRAMS (cfun), free_hist, NULL);
      htab_delete (VALUE_HISTOGRAMS (cfun));
      VALUE_HISTOGRAMS (cfun) = NULL;
    }
}


/* The overall number of invocations of the counter should match
   execution count of basic block.  Report it as error rather than
   internal error as it might mean that user has misused the profile
   somehow.  */

static bool
check_counter (gimple stmt, const char * name,
	       gcov_type *count, gcov_type *all, gcov_type bb_count)
{
  if (*all != bb_count || *count > *all)
    {
      location_t locus;
      locus = (stmt != NULL)
              ? gimple_location (stmt)
              : DECL_SOURCE_LOCATION (current_function_decl);
      if (flag_profile_correction)
        {
	  inform (locus, "Correcting inconsistent value profile: "
		  "%s profiler overall count (%d) does not match BB count "
                  "(%d)", name, (int)*all, (int)bb_count);
          /* For sample based value profile, it's quite likely that the
             value profile count is not consistent with the basic block count.
             In this case, we scale *all to bb_count, and scale *count
             accordingly.  */
          if (flag_sample_profile && *all > 0)
            *count *= (bb_count / *all);
	  *all = bb_count;
	  if (*count > *all)
            *count = *all;
	  return false;
	}
      else
	{
	  error_at (locus, "corrupted value profile: %s "
		    "profile counter (%d out of %d) inconsistent with "
		    "basic-block count (%d)",
		    name,
		    (int) *count,
		    (int) *all,
		    (int) bb_count);
	  return true;
	}
    }

  return false;
}

/* The overall number of invocations of the counter should match
   execution count of basic block.  Report it as error rather than
   internal error as it might mean that user has misused the profile
   somehow.  STMT is the indiret call, COUNT1 and COUNT2 are counts
   of two top targets, and ALL is the enclosing basic block execution
   count.  */

static bool
check_ic_counter (gimple stmt, gcov_type *count1, gcov_type *count2,
                  gcov_type all)
{
  location_t locus;
  if (*count1 > all && flag_profile_correction)
    {
      locus = (stmt != NULL)
              ? gimple_location (stmt)
              : DECL_SOURCE_LOCATION (current_function_decl);
      inform (locus, "Correcting inconsistent value profile: "
              "ic (topn) profiler top target count (%u) exceeds "
	      "BB count (%u)", (unsigned)*count1, (unsigned)all);
      *count1 = all;
    }
  if (*count2 > all && flag_profile_correction)
    {
      locus = (stmt != NULL)
              ? gimple_location (stmt)
              : DECL_SOURCE_LOCATION (current_function_decl);
      inform (locus, "Correcting inconsistent value profile: "
              "ic (topn) profiler second target count (%u) exceeds "
	      "BB count (%u)", (unsigned)*count2, (unsigned)all);
      *count2 = all;
    }
  
  if (*count2 > *count1)
    {
      locus = (stmt != NULL)
              ? gimple_location (stmt)
              : DECL_SOURCE_LOCATION (current_function_decl);
      inform (locus, "Corrupted topn ic value profile: "
	      "first target count (%u) is less than the second "
	      "target count (%u)", (unsigned)*count1, (unsigned)*count2);
      return true;
    }

  if (*count1 + *count2 > all)
    {
      /* If (COUNT1 + COUNT2) is greater than ALL by less than around 10% then
	 just fix COUNT2 up so that (COUNT1 + COUNT2) equals ALL.  */
      if ((*count1 + *count2 - all) < (all >> 3))
	*count2 = all - *count1;
      else
	{
	  locus = (stmt != NULL)
	    ? gimple_location (stmt)
	    : DECL_SOURCE_LOCATION (current_function_decl);
	  inform (locus, "Corrupted topn ic value profile: top two targets's"
		  " total count (%u) exceeds bb count (%u)",
		  (unsigned)(*count1 + *count2), (unsigned)all);
	  return true;
	}
    }
  return false;
}

/* Process the math functions given by --ffvpt-functions=.  */
struct ffvpt_options_s
ffvtp_process_options (const char *arg)
{
  const char *start = arg;

  struct ffvpt_options_s ffvpt_options;
  ffvpt_options.exp_set = 0;
  ffvpt_options.log_set = 0;
  ffvpt_options.pow_set = 0;
  ffvpt_options.sqrt_set = 0;

  while (*start)
    {
      if (strncmp ("all", start, 3) == 0
          && (start[4] == '\0' || start[3] == ','))
        {
          ffvpt_options.exp_set = 1;
          ffvpt_options.log_set = 1;
          ffvpt_options.pow_set = 1;
          ffvpt_options.sqrt_set = 1;
          break;
        }

      if (strncmp ("exp", start, 3) == 0
          && (start[3] == '\0' || start[3] == ','))
        ffvpt_options.exp_set = 1;
      else if (strncmp ("log", start, 3) == 0
               && (start[3] == '\0' || start[3] == ','))
        ffvpt_options.log_set = 1;
      else if (strncmp ("pow", start, 3) == 0
               && (start[3] == '\0' || start[3] == ','))
        ffvpt_options.pow_set = 1;
      else if (strncmp ("sqrt", start, 4) == 0
               && (start[4] == '\0' || start[4] == ','))
        ffvpt_options.sqrt_set = 1;
      else
        warning (0, "Unsupported function in the beginning of: %qs", start);
      start = strchr (start,',');
      if (start != NULL)
        ++start;
      else
        break;
    }
  return ffvpt_options;
}

/* Return if flags allow for ffvpt optimizations. */
static bool
do_float_value_profile_transformations (void)
{
  return flag_float_value_profile_transformations
      && (ffvpt_options.exp_set
          || ffvpt_options.log_set
          || ffvpt_options.pow_set
          || ffvpt_options.sqrt_set);
}



/* GIMPLE based transformations. */

static bool
gimple_value_profile_transformations (void)
{
  basic_block bb;
  gimple_stmt_iterator gsi;
  bool changed = false;
  int hot_self_insns = 0;

  /* Now that we have edge profile information, update the node
     summary.  */
  estimate_num_insns_fn (current_function_decl,
                         &eni_inlining_weights,
                         &hot_self_insns);
  cgraph_node (current_function_decl)->local.inline_summary.self_hot_insns
      = hot_self_insns;
  FOR_EACH_BB (bb)
    {
      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  gimple stmt = gsi_stmt (gsi);
	  histogram_value th = gimple_histogram_value (cfun, stmt);
	  if (!th)
	    continue;

	  if (dump_file)
	    {
	      fprintf (dump_file, "Trying transformations on stmt ");
	      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
	      dump_histograms_for_stmt (cfun, dump_file, stmt);
	    }

	  /* Transformations:  */
	  /* The order of things in this conditional controls which
	     transformation is used when more than one is applicable.  */
	  /* It is expected that any code added by the transformations
	     will be added before the current statement, and that the
	     current statement remain valid (although possibly
	     modified) upon return.  */
	  if (flag_value_profile_transformations
	      && ((gimple_mod_subtract_transform (&gsi)
                   || gimple_divmod_fixed_value_transform (&gsi)
                   || gimple_mod_pow2_value_transform (&gsi)
                   || gimple_stringops_transform (&gsi)
                   || gimple_ic_transform (stmt))
                  || (do_float_value_profile_transformations ()
                      && gimple_float_math_call_transform (&gsi))))
            {
	      stmt = gsi_stmt (gsi);
	      changed = true;
	      /* Original statement may no longer be in the same block. */
	      if (bb != gimple_bb (stmt))
		{
	          bb = gimple_bb (stmt);
		  gsi = gsi_for_stmt (stmt);
		}
	    }
        }
    }

  if (changed)
    {
      counts_to_freqs ();
      /* Value profile transformations may change inline parameters
         a lot (e.g., indirect call promotion introduces new direct calls).
         The update is also needed to avoid compiler ICE -- when MULTI
         target icall promotion happens, the caller's size may become
         negative when the promoted direct calls get promoted.  */
      /* Guard this for LIPO for now.  */
      if (L_IPO_COMP_MODE)
        compute_inline_parameters (cgraph_node (current_function_decl));
    }

  return changed;
}


/* Generate code for transformation 1 (with parent gimple assignment
   STMT and probability of taking the optimal path PROB, which is
   equivalent to COUNT/ALL within roundoff error).  This generates the
   result into a temp and returns the temp; it does not replace or
   alter the original STMT.  */

static tree
gimple_divmod_fixed_value (gimple stmt, tree value, int prob, gcov_type count,
			   gcov_type all)
{
  gimple stmt1, stmt2, stmt3;
  tree tmp1, tmp2, tmpv;
  gimple bb1end, bb2end, bb3end;
  basic_block bb, bb2, bb3, bb4;
  tree optype, op1, op2;
  edge e12, e13, e23, e24, e34;
  gimple_stmt_iterator gsi;

  gcc_assert (is_gimple_assign (stmt)
	      && (gimple_assign_rhs_code (stmt) == TRUNC_DIV_EXPR
		  || gimple_assign_rhs_code (stmt) == TRUNC_MOD_EXPR));

  optype = TREE_TYPE (gimple_assign_lhs (stmt));
  op1 = gimple_assign_rhs1 (stmt);
  op2 = gimple_assign_rhs2 (stmt);

  bb = gimple_bb (stmt);
  gsi = gsi_for_stmt (stmt);

  tmpv = create_tmp_var (optype, "PROF");
  tmp1 = create_tmp_var (optype, "PROF");
  stmt1 = gimple_build_assign (tmpv, fold_convert (optype, value));
  stmt2 = gimple_build_assign (tmp1, op2);
  stmt3 = gimple_build_cond (NE_EXPR, tmp1, tmpv, NULL_TREE, NULL_TREE);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt3, GSI_SAME_STMT);
  bb1end = stmt3;

  tmp2 = create_tmp_var (optype, "PROF");
  stmt1 = gimple_build_assign_with_ops (gimple_assign_rhs_code (stmt), tmp2,
					op1, tmpv);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  bb2end = stmt1;

  stmt1 = gimple_build_assign_with_ops (gimple_assign_rhs_code (stmt), tmp2,
					op1, op2);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  bb3end = stmt1;

  /* Fix CFG. */
  /* Edge e23 connects bb2 to bb3, etc. */
  e12 = split_block (bb, bb1end);
  bb2 = e12->dest;
  bb2->count = count;
  e23 = split_block (bb2, bb2end);
  bb3 = e23->dest;
  bb3->count = all - count;
  e34 = split_block (bb3, bb3end);
  bb4 = e34->dest;
  bb4->count = all;

  e12->flags &= ~EDGE_FALLTHRU;
  e12->flags |= EDGE_FALSE_VALUE;
  e12->probability = prob;
  e12->count = count;

  e13 = make_edge (bb, bb3, EDGE_TRUE_VALUE);
  e13->probability = REG_BR_PROB_BASE - prob;
  e13->count = all - count;

  remove_edge (e23);

  e24 = make_edge (bb2, bb4, EDGE_FALLTHRU);
  e24->probability = REG_BR_PROB_BASE;
  e24->count = count;

  e34->probability = REG_BR_PROB_BASE;
  e34->count = all - count;

  return tmp2;
}


/* Replace a math function call with a series of statements that check
   for a specific input value and if found, use a precalculated value.
e.g.:
     a = fn(b)
-->
     if (b == k_1):     // bb1
       a = k2           // bb2
     else
       a = fn(b)        // bb3
                        // bb4
*/
static tree
gimple_ffvpt_update_math_calls (gimple stmt, tree value, int prob,
                                gcov_type count, gcov_type all,
                                tree new_value_expr)
{

  gimple stmt1, stmt2, stmt3;
  tree tmp_b, tmp_a, tmp_k1;
  gimple bb1end, bb2end, bb3end;
  basic_block bb, bb2, bb3, bb4;
  tree optype; /* , calltree; */
  edge e12, e13, e23, e24, e34;
  gimple_stmt_iterator gsi;

  gcc_assert (is_gimple_call (stmt));

  optype = TREE_TYPE (gimple_assign_lhs (stmt)); /* double variable */

  bb = gimple_bb (stmt);
  gsi = gsi_for_stmt (stmt);

  tmp_k1 = create_tmp_var (optype, "PROF");
  tmp_b = create_tmp_var (optype, "PROF");
  stmt1 = gimple_build_assign (tmp_k1, fold_convert (optype, value));
  /* Get the value from the call.  */
  stmt2 = gimple_build_assign (tmp_b, gimple_call_arg (stmt, 0));
  stmt3 = gimple_build_cond (NE_EXPR, tmp_b, tmp_k1, NULL_TREE, NULL_TREE);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt3, GSI_SAME_STMT);
  bb1end = stmt3;
  /* a = k_2  */
  tmp_a = gimple_get_lhs (stmt);
  stmt1 = gimple_build_assign (tmp_a, new_value_expr);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  bb2end = stmt1;
  bb3end = stmt;
  /* Fix CFG. */
  /* Edge e23 connects bb2 to bb3, etc. */
  e12 = split_block (bb, bb1end);
  bb2 = e12->dest;
  bb2->count = count;
  e23 = split_block (bb2, bb2end);
  bb3 = e23->dest;
  bb3->count = all - count;
  e34 = split_block (bb3, bb3end);
  bb4 = e34->dest;
  bb4->count = all;

  e12->flags &= ~EDGE_FALLTHRU;
  e12->flags |= EDGE_FALSE_VALUE;
  e12->probability = prob;
  e12->count = count;
  e13 = make_edge (bb, bb3, EDGE_TRUE_VALUE);
  e13->probability = REG_BR_PROB_BASE - prob;
  e13->count = all - count;

  remove_edge (e23);

  e24 = make_edge (bb2, bb4, EDGE_FALLTHRU);
  e24->probability = REG_BR_PROB_BASE;
  e24->count = count;
  e34->probability = REG_BR_PROB_BASE;
  e34->count = all - count;

  return value;
}

/* Return a REAL_VALUE from gcov_type representing a double.  */
static REAL_VALUE_TYPE
gen_real_from_gcov_type (gcov_type g)
{
  int len = 8;
  unsigned char ptr[8];
  REAL_VALUE_TYPE r;
  int i;
  for (i = 0; i < 8; ++i)
    {
      ptr[i] = g & 0xff;
      g = g >> 8;
    }
  if (!real_from_native (double_type_node, ptr, len, &r))
    warning (0, "Error converting value to real.");

  return r;
}

static tree
gimple_float_pow_call (gimple stmt, double arg2, int prob, gcov_type count,
                       gcov_type all)
{
  tree tree_arg2;
  REAL_VALUE_TYPE r;

  r = gen_real_from_gcov_type (gcov_float_to_type (arg2));

  tree_arg2 = build_real (get_gcov_float_t (), r);

  if (arg2 == 0.0 || arg2 == 1.0 || arg2 == 2.0) {
    /* convert:
         a = pow(x,y)
       to:
         if (y == 0.0 | 1.0 | 2.0): // bb1
           a = 1.0 | x | x*x        // bb2
         else
           a = pow(x,y)             // bb3
                                    // bb4
   */
    gimple stmt1, stmt2, stmt3;
    tree tmp_b, tmp_a, tmp_k1;
    gimple bb1end, bb2end, bb3end;
    basic_block bb, bb2, bb3, bb4;
    tree optype;
    edge e12, e13, e23, e24, e34;
    gimple_stmt_iterator gsi;


    gcc_assert (is_gimple_call (stmt));

    optype = TREE_TYPE (gimple_assign_lhs (stmt)); /*double variable */
    bb = gimple_bb (stmt);
    gsi = gsi_for_stmt (stmt);

    tmp_k1 = create_tmp_var (optype, "PROF");
    tmp_b = create_tmp_var (optype, "PROF");
    stmt1 = gimple_build_assign (tmp_k1, fold_convert (optype, tree_arg2));
    /*get the value from the call */
    stmt2 = gimple_build_assign (tmp_b, gimple_call_arg (stmt, 1));
    stmt3 = gimple_build_cond (NE_EXPR, tmp_b, tmp_k1, NULL_TREE, NULL_TREE);
    gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
    gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
    gsi_insert_before (&gsi, stmt3, GSI_SAME_STMT);
    bb1end = stmt3;

    /* a = 1.0  */
    tmp_a = gimple_get_lhs (stmt);
    if (arg2 == 0.0) {
      tree tree_one;
      r = gen_real_from_gcov_type (gcov_float_to_type (1.0));
      tree_one = build_real (get_gcov_float_t (), r);
      stmt1 = gimple_build_assign (tmp_a, tree_one);
    } else if (arg2 == 1.0) {
      /* pow (x, 1.0) => x */
      tree tree_x = gimple_call_arg (stmt, 0);
      stmt1 = gimple_build_assign (tmp_a, tree_x);
    } else if (arg2 == 2.0) {
      /* pow (x, 2.0) => x*x */
      tree tree_x = gimple_call_arg (stmt, 0);
      stmt1 = gimple_build_assign_with_ops (MULT_EXPR, tmp_a, tree_x, tree_x);
    } else {
      gcc_unreachable ();
    }

    gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
    bb2end = stmt1;
    bb3end = stmt;

    /* Fix CFG.  */
    /* Edge e23 connects bb2 to bb3, etc.  */
    e12 = split_block (bb, bb1end);
    bb2 = e12->dest;
    bb2->count = count;
    e23 = split_block (bb2, bb2end);
    bb3 = e23->dest;
    bb3->count = all - count;
    e34 = split_block (bb3, bb3end);
    bb4 = e34->dest;
    bb4->count = all;

    e12->flags &= ~EDGE_FALLTHRU;
    e12->flags |= EDGE_FALSE_VALUE;
    e12->probability = prob;
    e12->count = count;

    e13 = make_edge (bb, bb3, EDGE_TRUE_VALUE);
    e13->probability = REG_BR_PROB_BASE - prob;
    e13->count = all - count;

    remove_edge (e23);

    e24 = make_edge (bb2, bb4, EDGE_FALLTHRU);
    e24->probability = REG_BR_PROB_BASE;
    e24->count = count;

    e34->probability = REG_BR_PROB_BASE;
    e34->count = all - count;
  }

  return tree_arg2;
}


/* Do transform 1) on INSN if applicable.  */

static bool
gimple_divmod_fixed_value_transform (gimple_stmt_iterator *si)
{
  histogram_value histogram;
  enum tree_code code;
  gcov_type val, count, all;
  tree result, value, tree_val;
  gcov_type prob;
  gimple stmt;

  stmt = gsi_stmt (*si);
  if (gimple_code (stmt) != GIMPLE_ASSIGN)
    return false;

  if (!INTEGRAL_TYPE_P (TREE_TYPE (gimple_assign_lhs (stmt))))
    return false;

  code = gimple_assign_rhs_code (stmt);
  
  if (code != TRUNC_DIV_EXPR && code != TRUNC_MOD_EXPR)
    return false;

  histogram = gimple_histogram_value_of_type (cfun, stmt,
					      HIST_TYPE_SINGLE_VALUE);
  if (!histogram)
    return false;

  value = histogram->hvalue.value;
  val = histogram->hvalue.counters[0];
  count = histogram->hvalue.counters[1];
  all = histogram->hvalue.counters[2];
  gimple_remove_histogram_value (cfun, stmt, histogram);

  /* We require that count is at least half of all; this means
     that for the transformation to fire the value must be constant
     at least 50% of time (and 75% gives the guarantee of usage).  */
  if (simple_cst_equal (gimple_assign_rhs2 (stmt), value) != 1
      || 2 * count < all
      || optimize_bb_for_size_p (gimple_bb (stmt)))
    return false;

  if (check_counter (stmt, "value", &count, &all, gimple_bb (stmt)->count))
    return false;

  /* Compute probability of taking the optimal path.  */
  if (all > 0)
    prob = (count * REG_BR_PROB_BASE + all / 2) / all;
  else
    prob = 0;

  tree_val = build_int_cst_wide (get_gcov_type (),
				 (unsigned HOST_WIDE_INT) val,
				 val >> (HOST_BITS_PER_WIDE_INT - 1) >> 1);
  result = gimple_divmod_fixed_value (stmt, tree_val, prob, count, all);

  if (dump_file)
    {
      fprintf (dump_file, "Div/mod by constant ");
      print_generic_expr (dump_file, value, TDF_SLIM);
      fprintf (dump_file, "=");
      print_generic_expr (dump_file, tree_val, TDF_SLIM);
      fprintf (dump_file, " transformation on insn ");
      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
    }

  gimple_assign_set_rhs_from_tree (si, result);

  return true;
}

enum ffvpt_math_functions
{
  FFVPT_EXP_FUN,
  FFVPT_LOG_FUN,
  FFVPT_POW_FUN,
  FFVPT_SQRT_FUN,
  FFVPT_AMD_EXP_FUN,
  FFVPT_AMD_LOG_FUN,
  FFVPT_AMD_POW_FUN,
  FFVPT_AMD_SQRT_FUN,
  FFVPT_UNSUPPORTED_FUN
};

/* Return info if call is a math function that can be optimized by ffvpt.  */
static enum ffvpt_math_functions
get_ffvpt_math_function (gimple call, tree fndecl)
{
  tree id;
  int id_len;
  if (fndecl && DECL_NAME (fndecl) && TREE_PUBLIC (fndecl))
    {
      id = DECL_ASSEMBLER_NAME (fndecl);
      id_len = IDENTIFIER_LENGTH (id);
      if (id_len == 7 || id_len == 8 || id_len == 9)
        {
          const char *name = IDENTIFIER_POINTER (id);
          /* Validate name and type of functions.  */
          if (name[0] == 'a')
            {
              if (! strcmp (name, "amd_exp") || ! strcmp (name, "acml_exp"))
                {
                  if (validate_gimple_arglist (call, REAL_TYPE, VOID_TYPE))
                    return FFVPT_AMD_EXP_FUN;
                }
              else if (! strcmp (name, "amd_pow") || ! strcmp (name, "acml_pow"))
                {
                 if (validate_gimple_arglist (call, REAL_TYPE, REAL_TYPE,
                                              VOID_TYPE))
                   return FFVPT_AMD_POW_FUN;
                }
              else if (! strcmp (name, "amd_log") || ! strcmp (name, "acml_log"))
                {
                  if (validate_gimple_arglist (call, REAL_TYPE, VOID_TYPE))
                    return FFVPT_AMD_LOG_FUN;
                }
              else if (! strcmp (name, "amd_sqrt")
                       || ! strcmp (name, "acml_sqrt"))
                {
                  if (validate_gimple_arglist (call, REAL_TYPE, VOID_TYPE))
                    return FFVPT_AMD_SQRT_FUN;
                }
            }
        }
    }

  if (!DECL_BUILT_IN (fndecl)
      || (DECL_BUILT_IN_CLASS (fndecl) != BUILT_IN_NORMAL))
    return FFVPT_UNSUPPORTED_FUN;

  switch (DECL_FUNCTION_CODE (fndecl))
    {
      CASE_FLT_FN (BUILT_IN_EXP):
          return FFVPT_EXP_FUN;
      CASE_FLT_FN (BUILT_IN_LOG):
          return FFVPT_LOG_FUN;
      CASE_FLT_FN (BUILT_IN_SQRT):
          return FFVPT_SQRT_FUN;
      CASE_FLT_FN (BUILT_IN_POW):
          return FFVPT_POW_FUN;
    }
  return FFVPT_UNSUPPORTED_FUN;
}


static bool
gimple_float_math_call_transform (gimple_stmt_iterator *si)
{
  histogram_value histogram;
  gcov_type val, count, all;
  gcov_float_t val_f;
  tree value;
  tree result;

  gcov_type prob;
  gimple stmt;
  tree fndecl;
  tree arg1;

  double cal_result;

  int bln_precalculate = 0;

  REAL_VALUE_TYPE r;

  enum ffvpt_math_functions math_fun;

  stmt = gsi_stmt (*si);
  if (gimple_code (stmt) != GIMPLE_CALL)
    return false;

  fndecl = gimple_call_fndecl (stmt);
  if (fndecl == NULL)
    return false;

  math_fun = get_ffvpt_math_function (stmt, fndecl);
  switch (math_fun)
    {
      case FFVPT_UNSUPPORTED_FUN:
        /* Not a (supported) math function */
        break;
      case FFVPT_EXP_FUN:
      case FFVPT_AMD_EXP_FUN:
        if (!ffvpt_options.exp_set)
          return false;
        arg1 = gimple_call_arg (stmt, 0);
        break;
      case FFVPT_LOG_FUN:
      case FFVPT_AMD_LOG_FUN:
        if (!ffvpt_options.log_set)
          return false;
        arg1 = gimple_call_arg (stmt, 0);
        break;
      case FFVPT_POW_FUN:
      case FFVPT_AMD_POW_FUN:
        /* Profile the second argument */
        if (!ffvpt_options.pow_set)
          return false;
        arg1 = gimple_call_arg (stmt, 1);
        break;
      case FFVPT_SQRT_FUN:
      case FFVPT_AMD_SQRT_FUN:
        if (!ffvpt_options.sqrt_set)
          return false;
        arg1 = gimple_call_arg (stmt, 0);
        break;
      default:
        gcc_unreachable ();
    }

  histogram = gimple_histogram_value_of_type (cfun, stmt,
					      HIST_TYPE_SINGLE_FLOAT_VALUE);
  if (!histogram)
    return false;

  value = histogram->hvalue.value;
  val = histogram->hvalue.counters[0];
  val_f = gcov_type_to_float (val);

  count = histogram->hvalue.counters[1];
  all = histogram->hvalue.counters[2];
  gimple_remove_histogram_value (cfun, stmt, histogram);

  /* We require that count is at least half of all; this means
     that for the transformation to fire the value must be constant
     at least 50% of time (and 75% gives the guarantee of usage).  */
  if (all == 0 || 2 * count < all) {
    if (dump_file)
      {
        fprintf (dump_file, "Not enough count: %ld all: %ld\n", count, all);
      }
    return false;
  }

  if (check_counter (stmt, "value", &count, &all, gimple_bb (stmt)->count)) {
    if (dump_file)
      {
        fprintf (dump_file, "check counter failed\n");
      }
    return false;
  }

  /* Compute probability of taking the optimal path.  */
  prob = (count * REG_BR_PROB_BASE + all / 2) / all;

  switch (math_fun)
    {
      case FFVPT_EXP_FUN:
      case FFVPT_AMD_EXP_FUN:
        cal_result = exp (val_f);
        bln_precalculate = 1;
        break;
      case FFVPT_LOG_FUN:
      case FFVPT_AMD_LOG_FUN:
        cal_result = log (val_f);
        bln_precalculate = 1;
        break;
      case FFVPT_SQRT_FUN:
      case FFVPT_AMD_SQRT_FUN:
        cal_result = sqrt (val_f);
        bln_precalculate = 1;
        break;
      case FFVPT_POW_FUN:
      case FFVPT_AMD_POW_FUN:
        bln_precalculate = 0;
        break;
      default:
        /* Unsupported math function found. */
        gcc_unreachable ();
    }
  if (bln_precalculate)
    {
      tree tree_val;
      tree cal_tree;
      r = gen_real_from_gcov_type (val);
      tree_val = build_real (get_gcov_float_t (), r);
      r = gen_real_from_gcov_type (gcov_float_to_type (cal_result));
      cal_tree = build_real (get_gcov_float_t (), r);

      result = gimple_ffvpt_update_math_calls (stmt, tree_val, prob, count, all,
                                               cal_tree);
    }
  else if (bln_precalculate == 0)
    {
      /* Calls pow with second argument almost always a constant...*/
      /* tree tree_arg_1; */
      if (val_f == 0.0)
        {
          /* Replace with 1.00! */
          result = gimple_float_pow_call (stmt, val_f, prob, count, all);
        }
      else if (val_f == 1.0)
        {
          /* Replace with first argument */
          result = gimple_float_pow_call (stmt, val_f, prob, count, all);
        }
      else if (val_f == 2.0)
        {
          /* Replace with first argument times itself */
          result = gimple_float_pow_call (stmt, val_f, prob, count, all);
        }
      else
        {
          /* TODO(martint): Consider optimizing other constants as well.
             For example 0.5 -> sqrt() */
          return false;
        }

    }
  if (dump_file)
    {
      if (bln_precalculate) {
        fprintf (dump_file,
                 "Math call (%s) to constant value: %f in %s (use %f) "
                 "(count:%ld, all:%ld)\n",
                 lang_hooks.decl_printable_name (fndecl, 1),
                 val_f,
                 current_function_name (),
                 cal_result,
                 count,
                 all);
      } else {
        fprintf (dump_file,
                 "Math call (%s) with constant argument (%f) optimized in %s: "
                 "(count:%ld, all:%ld)\n",
                 lang_hooks.decl_printable_name (fndecl, 1),
                 val_f,
                 current_function_name (),
                 count,
                 all);
      }
    }
  return true;
}

/* Generate code for transformation 2 (with parent gimple assign STMT and
   probability of taking the optimal path PROB, which is equivalent to COUNT/ALL
   within roundoff error).  This generates the result into a temp and returns 
   the temp; it does not replace or alter the original STMT.  */
static tree
gimple_mod_pow2 (gimple stmt, int prob, gcov_type count, gcov_type all)
{
  gimple stmt1, stmt2, stmt3, stmt4;
  tree tmp2, tmp3;
  gimple bb1end, bb2end, bb3end;
  basic_block bb, bb2, bb3, bb4;
  tree optype, op1, op2;
  edge e12, e13, e23, e24, e34;
  gimple_stmt_iterator gsi;
  tree result;

  gcc_assert (is_gimple_assign (stmt)
	      && gimple_assign_rhs_code (stmt) == TRUNC_MOD_EXPR);

  optype = TREE_TYPE (gimple_assign_lhs (stmt));
  op1 = gimple_assign_rhs1 (stmt);
  op2 = gimple_assign_rhs2 (stmt);

  bb = gimple_bb (stmt);
  gsi = gsi_for_stmt (stmt);

  result = create_tmp_var (optype, "PROF");
  tmp2 = create_tmp_var (optype, "PROF");
  tmp3 = create_tmp_var (optype, "PROF");
  stmt2 = gimple_build_assign_with_ops (PLUS_EXPR, tmp2, op2,
					build_int_cst (optype, -1));
  stmt3 = gimple_build_assign_with_ops (BIT_AND_EXPR, tmp3, tmp2, op2);
  stmt4 = gimple_build_cond (NE_EXPR, tmp3, build_int_cst (optype, 0),
			     NULL_TREE, NULL_TREE);
  gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt3, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt4, GSI_SAME_STMT);
  bb1end = stmt4;

  /* tmp2 == op2-1 inherited from previous block.  */
  stmt1 = gimple_build_assign_with_ops (BIT_AND_EXPR, result, op1, tmp2);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  bb2end = stmt1;

  stmt1 = gimple_build_assign_with_ops (gimple_assign_rhs_code (stmt), result,
					op1, op2);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  bb3end = stmt1;

  /* Fix CFG. */
  /* Edge e23 connects bb2 to bb3, etc. */
  e12 = split_block (bb, bb1end);
  bb2 = e12->dest;
  bb2->count = count;
  e23 = split_block (bb2, bb2end);
  bb3 = e23->dest;
  bb3->count = all - count;
  e34 = split_block (bb3, bb3end);
  bb4 = e34->dest;
  bb4->count = all;

  e12->flags &= ~EDGE_FALLTHRU;
  e12->flags |= EDGE_FALSE_VALUE;
  e12->probability = prob;
  e12->count = count;

  e13 = make_edge (bb, bb3, EDGE_TRUE_VALUE);
  e13->probability = REG_BR_PROB_BASE - prob;
  e13->count = all - count;

  remove_edge (e23);
  
  e24 = make_edge (bb2, bb4, EDGE_FALLTHRU);
  e24->probability = REG_BR_PROB_BASE;
  e24->count = count;

  e34->probability = REG_BR_PROB_BASE;
  e34->count = all - count;

  return result;
}

/* Do transform 2) on INSN if applicable.  */
static bool
gimple_mod_pow2_value_transform (gimple_stmt_iterator *si)
{
  histogram_value histogram;
  enum tree_code code;
  gcov_type count, wrong_values, all;
  tree lhs_type, result, value;
  gcov_type prob;
  gimple stmt;

  stmt = gsi_stmt (*si);
  if (gimple_code (stmt) != GIMPLE_ASSIGN)
    return false;

  lhs_type = TREE_TYPE (gimple_assign_lhs (stmt));
  if (!INTEGRAL_TYPE_P (lhs_type))
    return false;

  code = gimple_assign_rhs_code (stmt);
  
  if (code != TRUNC_MOD_EXPR || !TYPE_UNSIGNED (lhs_type))
    return false;

  histogram = gimple_histogram_value_of_type (cfun, stmt, HIST_TYPE_POW2);
  if (!histogram)
    return false;

  value = histogram->hvalue.value;
  wrong_values = histogram->hvalue.counters[0];
  count = histogram->hvalue.counters[1];

  gimple_remove_histogram_value (cfun, stmt, histogram);

  /* We require that we hit a power of 2 at least half of all evaluations.  */
  if (simple_cst_equal (gimple_assign_rhs2 (stmt), value) != 1
      || count < wrong_values
      || optimize_bb_for_size_p (gimple_bb (stmt)))
    return false;

  if (dump_file)
    {
      fprintf (dump_file, "Mod power of 2 transformation on insn ");
      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
    }

  /* Compute probability of taking the optimal path.  */
  all = count + wrong_values;

  if (check_counter (stmt, "pow2", &count, &all, gimple_bb (stmt)->count))
    return false;

  if (all > 0)
    prob = (count * REG_BR_PROB_BASE + all / 2) / all;
  else
    prob = 0;

  result = gimple_mod_pow2 (stmt, prob, count, all);

  gimple_assign_set_rhs_from_tree (si, result);

  return true;
}

/* Generate code for transformations 3 and 4 (with parent gimple assign STMT, and
   NCOUNTS the number of cases to support.  Currently only NCOUNTS==0 or 1 is
   supported and this is built into this interface.  The probabilities of taking
   the optimal paths are PROB1 and PROB2, which are equivalent to COUNT1/ALL and
   COUNT2/ALL respectively within roundoff error).  This generates the 
   result into a temp and returns the temp; it does not replace or alter 
   the original STMT.  */
/* FIXME: Generalize the interface to handle NCOUNTS > 1.  */

static tree
gimple_mod_subtract (gimple stmt, int prob1, int prob2, int ncounts,
		     gcov_type count1, gcov_type count2, gcov_type all)
{
  gimple stmt1, stmt2, stmt3;
  tree tmp1;
  gimple bb1end, bb2end = NULL, bb3end;
  basic_block bb, bb2, bb3, bb4;
  tree optype, op1, op2;
  edge e12, e23 = 0, e24, e34, e14;
  gimple_stmt_iterator gsi;
  tree result;

  gcc_assert (is_gimple_assign (stmt)
	      && gimple_assign_rhs_code (stmt) == TRUNC_MOD_EXPR);

  optype = TREE_TYPE (gimple_assign_lhs (stmt));
  op1 = gimple_assign_rhs1 (stmt);
  op2 = gimple_assign_rhs2 (stmt);

  bb = gimple_bb (stmt);
  gsi = gsi_for_stmt (stmt);

  result = create_tmp_var (optype, "PROF");
  tmp1 = create_tmp_var (optype, "PROF");
  stmt1 = gimple_build_assign (result, op1);
  stmt2 = gimple_build_assign (tmp1, op2);
  stmt3 = gimple_build_cond (LT_EXPR, result, tmp1, NULL_TREE, NULL_TREE);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt3, GSI_SAME_STMT);
  bb1end = stmt3;

  if (ncounts)	/* Assumed to be 0 or 1 */
    {
      stmt1 = gimple_build_assign_with_ops (MINUS_EXPR, result, result, tmp1);
      stmt2 = gimple_build_cond (LT_EXPR, result, tmp1, NULL_TREE, NULL_TREE);
      gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
      gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
      bb2end = stmt2;
    }

  /* Fallback case. */
  stmt1 = gimple_build_assign_with_ops (gimple_assign_rhs_code (stmt), result,
					result, tmp1);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  bb3end = stmt1;

  /* Fix CFG. */
  /* Edge e23 connects bb2 to bb3, etc. */
  /* However block 3 is optional; if it is not there, references
     to 3 really refer to block 2. */
  e12 = split_block (bb, bb1end);
  bb2 = e12->dest;
  bb2->count = all - count1;
    
  if (ncounts)	/* Assumed to be 0 or 1.  */
    {
      e23 = split_block (bb2, bb2end);
      bb3 = e23->dest;
      bb3->count = all - count1 - count2;
    }

  e34 = split_block (ncounts ? bb3 : bb2, bb3end);
  bb4 = e34->dest;
  bb4->count = all;

  e12->flags &= ~EDGE_FALLTHRU;
  e12->flags |= EDGE_FALSE_VALUE;
  e12->probability = REG_BR_PROB_BASE - prob1;
  e12->count = all - count1;

  e14 = make_edge (bb, bb4, EDGE_TRUE_VALUE);
  e14->probability = prob1;
  e14->count = count1;

  if (ncounts)  /* Assumed to be 0 or 1.  */
    {
      e23->flags &= ~EDGE_FALLTHRU;
      e23->flags |= EDGE_FALSE_VALUE;
      e23->count = all - count1 - count2;
      e23->probability = REG_BR_PROB_BASE - prob2;

      e24 = make_edge (bb2, bb4, EDGE_TRUE_VALUE);
      e24->probability = prob2;
      e24->count = count2;
    }

  e34->probability = REG_BR_PROB_BASE;
  e34->count = all - count1 - count2;

  return result;
}


/* Do transforms 3) and 4) on the statement pointed-to by SI if applicable.  */

static bool
gimple_mod_subtract_transform (gimple_stmt_iterator *si)
{
  histogram_value histogram;
  enum tree_code code;
  gcov_type count, wrong_values, all;
  tree lhs_type, result, value;
  gcov_type prob1, prob2;
  unsigned int i, steps;
  gcov_type count1, count2;
  gimple stmt;

  stmt = gsi_stmt (*si);
  if (gimple_code (stmt) != GIMPLE_ASSIGN)
    return false;

  lhs_type = TREE_TYPE (gimple_assign_lhs (stmt));
  if (!INTEGRAL_TYPE_P (lhs_type))
    return false;

  code = gimple_assign_rhs_code (stmt);
  
  if (code != TRUNC_MOD_EXPR || !TYPE_UNSIGNED (lhs_type))
    return false;

  histogram = gimple_histogram_value_of_type (cfun, stmt, HIST_TYPE_INTERVAL);
  if (!histogram)
    return false;

  value = histogram->hvalue.value;
  all = 0;
  wrong_values = 0;
  for (i = 0; i < histogram->hdata.intvl.steps; i++)
    all += histogram->hvalue.counters[i];

  wrong_values += histogram->hvalue.counters[i];
  wrong_values += histogram->hvalue.counters[i+1];
  steps = histogram->hdata.intvl.steps;
  all += wrong_values;
  count1 = histogram->hvalue.counters[0];
  count2 = histogram->hvalue.counters[1];

  /* Compute probability of taking the optimal path.  */
  if (check_counter (stmt, "interval", &count1, &all, gimple_bb (stmt)->count))
    {
      gimple_remove_histogram_value (cfun, stmt, histogram);
      return false;
    }

  if (flag_profile_correction && count1 + count2 > all)
      all = count1 + count2;

  gcc_assert (count1 + count2 <= all);

  /* We require that we use just subtractions in at least 50% of all
     evaluations.  */
  count = 0;
  for (i = 0; i < histogram->hdata.intvl.steps; i++)
    {
      count += histogram->hvalue.counters[i];
      if (count * 2 >= all)
	break;
    }
  if (i == steps
      || optimize_bb_for_size_p (gimple_bb (stmt)))
    return false;

  gimple_remove_histogram_value (cfun, stmt, histogram);
  if (dump_file)
    {
      fprintf (dump_file, "Mod subtract transformation on insn ");
      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
    }

  /* Compute probability of taking the optimal path(s).  */
  if (all > 0)
    {
      prob1 = (count1 * REG_BR_PROB_BASE + all / 2) / all;
      prob2 = (count2 * REG_BR_PROB_BASE + all / 2) / all;
    }
  else
    {
      prob1 = prob2 = 0;
    }

  /* In practice, "steps" is always 2.  This interface reflects this,
     and will need to be changed if "steps" can change.  */
  result = gimple_mod_subtract (stmt, prob1, prob2, i, count1, count2, all);

  gimple_assign_set_rhs_from_tree (si, result);

  return true;
}

static struct cgraph_node** pid_map = NULL;

/* Initialize map of pids (pid -> cgraph node) */

static void 
init_pid_map (void)
{
  struct cgraph_node *n;

  if (pid_map != NULL)
    return;

  pid_map = XCNEWVEC (struct cgraph_node*, cgraph_max_pid);

  for (n = cgraph_nodes; n; n = n->next)
    {
      if (n->pid != -1)
	pid_map [n->pid] = n;
    }
}

/* Return cgraph node for function with pid */

static inline struct cgraph_node*
find_func_by_pid (int pid)
{
  init_pid_map ();

  return pid_map [pid];
}


/* Remove a cgraph node from the map of pids */

void
cgraph_remove_pid (struct cgraph_node *n)
{
  if (pid_map == NULL || n->pid < 0)
    return;

  pid_map [n->pid] = NULL;
}


/* Initialize map of gids (gid -> cgraph node) */

static htab_t gid_map = NULL;

typedef struct func_gid_entry
{
  struct cgraph_node *node;
  unsigned HOST_WIDEST_INT gid;
} func_gid_entry_t;

/* Hash function for function global unique ids.  */

static hashval_t 
htab_gid_hash (const void * ent)
{
  const func_gid_entry_t *const entry = (const func_gid_entry_t *) ent;
  return entry->gid;
}

/* Hash table equality function for function global unique ids.  */

static int
htab_gid_eq (const void *ent1, const void * ent2)
{
  const func_gid_entry_t *const entry1 = (const func_gid_entry_t *) ent1;
  const func_gid_entry_t *const entry2 = (const func_gid_entry_t *) ent2;
  return entry1->gid == entry2->gid;
}

static void
htab_gid_del (void *ent)
{
  func_gid_entry_t *const entry = (func_gid_entry_t *) ent;
  free (entry);
}

/* Initialize the global unique id map for functions.  */

static void
init_gid_map (void)
{
  struct cgraph_node *n;

  gcc_assert (!gid_map);

  gid_map
      = htab_create (10, htab_gid_hash, htab_gid_eq, htab_gid_del);

  for (n = cgraph_nodes; n; n = n->next)
    {
      func_gid_entry_t ent, *entp;
      func_gid_entry_t **slot;
      struct function *f;
      ent.node = n;
      f = DECL_STRUCT_FUNCTION (n->decl);
      /* Do not care to indirect call promote a function with id.  */
      if (!f || DECL_ABSTRACT (n->decl))
        continue;
      /* The global function id computed at profile-use time
         is slightly different from the one computed in
         instrumentation runtime -- for the latter, the intra-
         module function ident is 1 based while in profile-use
         phase, it is zero based. See get_next_funcdef_no in
         function.c.  */
      ent.gid = FUNC_DECL_GLOBAL_ID (DECL_STRUCT_FUNCTION (n->decl));
      slot = (func_gid_entry_t **) htab_find_slot (gid_map, &ent, INSERT);

      gcc_assert (!*slot || ((*slot)->gid == ent.gid && (*slot)->node == n));
      if (!*slot)
        {
          *slot = entp = XCNEW (func_gid_entry_t);
          entp->node = n;
          entp->gid = ent.gid;
        }
    }
}

/* Initialize the global unique id map for functions.  */

void
cgraph_init_gid_map (void)
{
  if (!L_IPO_COMP_MODE)
    return;

  init_gid_map ();
}

/* Return cgraph node for function with global id.  */

struct cgraph_node *
find_func_by_global_id (unsigned HOST_WIDE_INT gid)
{
  func_gid_entry_t ent, *entp;

  gcc_assert (gid_map);

  ent.node = NULL;
  ent.gid = gid;
  entp = (func_gid_entry_t *)htab_find (gid_map, &ent);
  if (entp)
    return entp->node;
  return NULL;
}

/* Return cgraph node for function with name. We need this because
   sample based FDO doesn't record the function id for each function
   in the profile.
   TODO: need to transform this lookup method to hash table.  */

struct cgraph_node *
find_func_by_name (const char *name)
{
  struct cgraph_node *node = NULL;
  int len = strlen (name);

  for (node = cgraph_nodes; node; node = node->next) {
    const char *fname = IDENTIFIER_POINTER (decl_assembler_name (node->decl));
    if (!node->global.inlined_to
        && node->analyzed
        && node->master_clone == node
        && !strncmp(fname, name, len)
        && (!strncmp(fname + len, "_cmo_", 5) || fname[len] == 0
            || fname[len] == '.'))
      break;
  }
  return node;
}

/* Counts the number of arguments in the function_decl FN_DECL.

   Returns the number of arguments.  */
static unsigned
function_decl_num_args (tree fn_decl)
{
  tree arg;
  unsigned count = 0;
  for (arg = DECL_ARGUMENTS (fn_decl); arg; arg = TREE_CHAIN (arg))
    count++;
  return count;
}

/* Perform sanity check on the indirect call target. Due to race conditions,
   false function target may be attributed to an indirect call site. If the
   call expression type mismatches with the target function's type, expand_call
   may ICE. Here we only do very minimal sanity check just to make compiler happy.
   Returns true if TARGET is considered ok for call CALL_STMT.  */

static bool
check_ic_target (gimple call_stmt, struct cgraph_node *target)
{
  tree tgt_decl;
  /* Return types.  */
  tree icall_type, tgt_type; 
  tree call_expr;

  tgt_decl = target->decl;
  tgt_type = TREE_TYPE (TREE_TYPE (tgt_decl));

  call_expr = gimple_call_fn (call_stmt);
  icall_type = TREE_TYPE (call_expr);
  if (POINTER_TYPE_P (icall_type))
    icall_type = TREE_TYPE (icall_type);
  icall_type = TREE_TYPE (icall_type);

  if (TREE_CODE (icall_type) != TREE_CODE (tgt_type)
      || TYPE_MODE (icall_type) != TYPE_MODE (tgt_type))
    return false;

  /* Verify that CALL_STMT has the same number of arguments as TGT_TYPE. */
  if (gimple_call_num_args (call_stmt) != function_decl_num_args (tgt_decl))
    return false;

  /* Record types should have matching sizes. */
  if (TREE_CODE (icall_type) == RECORD_TYPE
      && TYPE_SIZE (icall_type) != NULL_TREE
      && TYPE_SIZE (tgt_type) != NULL_TREE
      && TREE_CODE (TYPE_SIZE (icall_type)) == INTEGER_CST
      && (TREE_CODE (TYPE_SIZE (tgt_type)) != INTEGER_CST ||
	  !tree_int_cst_equal (TYPE_SIZE (icall_type), TYPE_SIZE (tgt_type))))
    return false;

  return true;
}

/* Do transformation

  if (actual_callee_address == address_of_most_common_function/method)
    do direct call
  else
    old call
 */

static gimple
gimple_ic (gimple stmt, gimple call, struct cgraph_node *direct_call, 
	   int prob, gcov_type count, gcov_type all)
{
  gimple stmt1, stmt2, stmt3;
  tree tmp1, tmpv, tmp;
  gimple bb1end, bb2end, bb3end;
  basic_block bb, bb2, bb3, bb4;
  tree optype = build_pointer_type (void_type_node);
  edge e12, e13, e23, e24, e34;
  gimple_stmt_iterator gsi;
  int region;

  bb = gimple_bb (stmt);
  gsi = gsi_for_stmt (stmt);

  tmpv = create_tmp_var (optype, "PROF");
  tmp1 = create_tmp_var (optype, "PROF");
  stmt1 = gimple_build_assign (tmpv, unshare_expr (gimple_call_fn (call)));

  tmp = fold_convert (optype, build_addr (direct_call->decl, 
					  current_function_decl));
  stmt2 = gimple_build_assign (tmp1, tmp);
  stmt3 = gimple_build_cond (NE_EXPR, tmp1, tmpv, NULL_TREE, NULL_TREE);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt3, GSI_SAME_STMT);
  bb1end = stmt3;

  stmt1 = gimple_copy (stmt);
  gimple_call_set_fndecl (stmt1, direct_call->decl);
  /* Update call attribute.  */
  gimple_call_set_cannot_inline (stmt1, false);
  check_call_args (stmt1);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  bb2end = stmt1;
  bb3end = stmt;

  /* Fix CFG. */
  /* Edge e23 connects bb2 to bb3, etc. */
  e12 = split_block (bb, bb1end);
  bb2 = e12->dest;
  bb2->count = count;
  e23 = split_block (bb2, bb2end);
  bb3 = e23->dest;
  bb3->count = all - count;
  e34 = split_block (bb3, bb3end);
  bb4 = e34->dest;
  bb4->count = all;

  e12->flags &= ~EDGE_FALLTHRU;
  e12->flags |= EDGE_FALSE_VALUE;
  e12->probability = prob;
  e12->count = count;

  e13 = make_edge (bb, bb3, EDGE_TRUE_VALUE);
  e13->probability = REG_BR_PROB_BASE - prob;
  e13->count = all - count;

  remove_edge (e23);
  
  e24 = make_edge (bb2, bb4, EDGE_FALLTHRU);
  e24->probability = REG_BR_PROB_BASE;
  e24->count = count;
  e34->probability = REG_BR_PROB_BASE;
  e34->count = all - count;

  /* Fix eh edges */
  region = lookup_stmt_eh_region (stmt);
  if (region >= 0 && stmt_could_throw_p (stmt1))
    {
      add_stmt_to_eh_region (stmt1, region);
      make_eh_edges (stmt1);
    }

  if (region >= 0 && stmt_could_throw_p (stmt))
    {
      gimple_purge_dead_eh_edges (bb4);
      make_eh_edges (stmt);
    }

  return stmt1;
}

/*
  For every checked indirect/virtual call determine if most common pid of
  function/class method has probability more than 50%. If yes modify code of
  this call to:
 */

static bool
gimple_ic_transform_single_targ (gimple stmt, histogram_value histogram)
{
  gcov_type val, count, all, bb_all;
  gcov_type prob;
  gimple modify;
  struct cgraph_node *direct_call;

  val = histogram->hvalue.counters [0];
  count = histogram->hvalue.counters [1];
  all = histogram->hvalue.counters [2];
  gimple_remove_histogram_value (cfun, stmt, histogram);

  if (4 * count <= 3 * all)
    return false;

  bb_all = gimple_bb (stmt)->count;
  /* The order of CHECK_COUNTER calls is important - 
     since check_counter can correct the third parameter
     and we want to make count <= all <= bb_all. */
  if ( check_counter (stmt, "ic", &all, &bb_all, bb_all)
      || check_counter (stmt, "ic", &count, &all, all))
    return false;

  if (all > 0)
    prob = (count * REG_BR_PROB_BASE + all / 2) / all;
  else
    prob = 0;
  direct_call = find_func_by_pid ((int)val);

  if (direct_call == NULL)
    return false;

  if (!check_ic_target (stmt, direct_call))
    return false;

  modify = gimple_ic (stmt, stmt, direct_call, prob, count, all);

  if (dump_file)
    {
      fprintf (dump_file, "Indirect call -> direct call ");
      print_generic_expr (dump_file, gimple_call_fn (stmt), TDF_SLIM);
      fprintf (dump_file, "=> ");
      print_generic_expr (dump_file, direct_call->decl, TDF_SLIM);
      fprintf (dump_file, " transformation on insn ");
      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
      fprintf (dump_file, " to ");
      print_gimple_stmt (dump_file, modify, 0, TDF_SLIM);
      fprintf (dump_file, "hist->count "HOST_WIDEST_INT_PRINT_DEC
	       " hist->all "HOST_WIDEST_INT_PRINT_DEC"\n", count, all);
    }

  return true;
}

/* Return true if CALLER is likely to be called within a loop and has
   large dynamic execution trace. There is high temporal locality for
   caller's instruction.  */

static bool
is_large_caller_with_possible_temporal_locality (struct cgraph_node *caller)
{
  struct function *func = DECL_STRUCT_FUNCTION (caller->decl);

  return (maybe_hot_bb_for_func_p (func,
                                   ENTRY_BLOCK_PTR_FOR_FUNCTION (func))
          && caller->local.inline_summary.self_hot_insns
          > PARAM_VALUE (PARAM_LARGE_FUNCTION_HOT_INSNS));;
}


/* Convert indirect function call STMT into guarded direct function
   calls. Multiple indirect call targets are supported. HISTOGRAM
   is the target distribution for the callsite.  */

static bool
gimple_ic_transform_mult_targ (gimple stmt, histogram_value histogram)
{
  gcov_type val1, val2, count1, count2, all, bb_all;
  gcov_type prob1, prob2;
  gimple modify1, modify2;
  struct cgraph_node *direct_call1 = 0, *direct_call2 = 0;
  int perc_threshold, count_threshold, always_inline;
  location_t locus;
  bool icache_sensitive = false;

  val1 = histogram->hvalue.counters [1];
  count1 = histogram->hvalue.counters [2];
  val2 = histogram->hvalue.counters [3];
  count2 = histogram->hvalue.counters [4];
  bb_all = flag_sample_profile ? histogram->hvalue.counters[0]:
                                 gimple_bb (stmt)->count;
  all = bb_all;

  gimple_remove_histogram_value (cfun, stmt, histogram);

  if (count1 == 0)
    return false;

  perc_threshold = PARAM_VALUE (PARAM_ICALL_PROMOTE_PERCENT_THRESHOLD);
  count_threshold = PARAM_VALUE (PARAM_ICALL_PROMOTE_COUNT_THRESHOLD);
  always_inline = PARAM_VALUE (PARAM_ALWAYS_INLINE_ICALL_TARGET);

  if (100 * count1 < all * perc_threshold || count1 < count_threshold)
    return false;

  if (check_ic_counter (stmt, &count1, &count2, all))
    return false;

  icache_sensitive = is_large_caller_with_possible_temporal_locality (
      cgraph_node (current_function_decl));

  if (all > 0)
    {
      prob1 = (count1 * REG_BR_PROB_BASE + all / 2) / all;
      if (all - count1 > 0)
        prob2 = (count2 * REG_BR_PROB_BASE
                 + (all - count1) / 2) / (all - count1);
      else
        prob2 = 0;
    }
  else
    prob1 = prob2 = 0;

  if (flag_sample_profile)
    direct_call1 = find_func_by_name ((char *)val1);
  else
    direct_call1 = find_func_by_global_id (val1);

  if (val2 && (100 * count2 >= all * perc_threshold)
      && count2 > count_threshold) {
    if (flag_sample_profile)
      direct_call2 = find_func_by_name ((char *)val2);
    else
      direct_call2 = find_func_by_global_id (val2);
  }

  locus = (stmt != NULL) ? gimple_location (stmt)
      : DECL_SOURCE_LOCATION (current_function_decl);
  if (direct_call1 == NULL
      || !check_ic_target (stmt, direct_call1))
    {
      if (flag_ripa_verbose)
        {
          if (!direct_call1)
            inform (locus, "Can not find indirect call target decl "
                    "(%d:%d)[cnt:%u] in current module",
                    EXTRACT_MODULE_ID_FROM_GLOBAL_ID (val1),
                    EXTRACT_FUNC_ID_FROM_GLOBAL_ID (val1), (unsigned) count1);
          else
            inform (locus,
                    "Can not find promote indirect call target decl -- type mismatch "
                    "(%d:%d)[cnt:%u] in current module",
                    EXTRACT_MODULE_ID_FROM_GLOBAL_ID (val1),
                    EXTRACT_FUNC_ID_FROM_GLOBAL_ID (val1), (unsigned) count1);
        }
      return false;
    }

  /* Don't indirect-call promote if the target is in auxiliary module and
     DECL_ARTIFICIAL and not TREE_PUBLIC, because we don't static-promote
     DECL_ARTIFICIALs yet.  */
  if (cgraph_is_auxiliary (direct_call1->decl)
      && DECL_ARTIFICIAL (direct_call1->decl)
      && ! TREE_PUBLIC (direct_call1->decl))
    return false;

  modify1 = gimple_ic (stmt, stmt, direct_call1, prob1, count1, all);
  if (flag_ripa_verbose)
    inform (locus, "Promote indirect call to target (call count:%u) %s",
            (unsigned) count1,
            lang_hooks.decl_printable_name (direct_call1->decl, 3));

  if (icache_sensitive)
    {
      if (dump_file)
        fprintf (dump_file, "=== Suppressing Inlining %s --> %s === \n",
                 cgraph_node_name (cgraph_node (current_function_decl)),
                 cgraph_node_name (direct_call1));
      gimple_call_set_cannot_inline (modify1, true);
    }

  if (always_inline && count1 >= always_inline)
    {
      /* TODO: should mark the call edge. */
      DECL_DISREGARD_INLINE_LIMITS (direct_call1->decl) = 1;
      direct_call1->local.disregard_inline_limits = 1;
    }
  if (dump_file)
    {
      fprintf (dump_file, "Indirect call -> direct call ");
      print_generic_expr (dump_file, gimple_call_fn (stmt), TDF_SLIM);
      fprintf (dump_file, "=> ");
      print_generic_expr (dump_file, direct_call1->decl, TDF_SLIM);
      if (flag_sample_profile)
        fprintf (dump_file, " (%s)\n", (char *)val1);
      else
        fprintf (dump_file, " (module_id:%d, func_id:%d)\n",
                 EXTRACT_MODULE_ID_FROM_GLOBAL_ID (val1),
                 EXTRACT_FUNC_ID_FROM_GLOBAL_ID (val1));
      fprintf (dump_file, "Transformation on insn:\n");
      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
      fprintf (dump_file, "==>\n");
      print_gimple_stmt (dump_file, modify1, 0, TDF_SLIM);
      fprintf (dump_file, "hist->count "HOST_WIDEST_INT_PRINT_DEC
	       " hist->all "HOST_WIDEST_INT_PRINT_DEC"\n", count1, all);
    }

  if (direct_call2 && check_ic_target (stmt, direct_call2)
      /* Don't indirect-call promote if the target is in auxiliary module and
	 DECL_ARTIFICIAL and not TREE_PUBLIC, because we don't static-promote
	 DECL_ARTIFICIALs yet.  */
      && ! (cgraph_is_auxiliary (direct_call2->decl)
	    && DECL_ARTIFICIAL (direct_call2->decl)
	    && ! TREE_PUBLIC (direct_call2->decl)))
    {
      modify2 = gimple_ic (stmt, stmt, direct_call2,
                           prob2, count2, all - count1);

      if (flag_ripa_verbose)
        inform (locus, "Promote indirect call to target (call count:%u) %s",
                (unsigned) count2,
                lang_hooks.decl_printable_name (direct_call2->decl, 3));

      if (icache_sensitive)
        {
          if (dump_file)
            fprintf (dump_file, "=== Suppressing Inlining %s --> %s === \n",
                     cgraph_node_name (cgraph_node (current_function_decl)),
                     cgraph_node_name (direct_call2));
          gimple_call_set_cannot_inline (modify2, true);
        }
      if (always_inline && count2 >= always_inline)
        {
          /* TODO: should mark the call edge.  */
          DECL_DISREGARD_INLINE_LIMITS (direct_call2->decl) = 1;
          direct_call2->local.disregard_inline_limits = 1;
        }
      if (dump_file)
        {
          fprintf (dump_file, "Indirect call -> direct call ");
          print_generic_expr (dump_file, gimple_call_fn (stmt), TDF_SLIM);
          fprintf (dump_file, "=> ");
          print_generic_expr (dump_file, direct_call2->decl, TDF_SLIM);
          if (flag_sample_profile)
            fprintf (dump_file, " (%s)\n", (char *)val2);
          else
            fprintf (dump_file, " (module_id:%d, func_id:%d)\n",
                     EXTRACT_MODULE_ID_FROM_GLOBAL_ID (val2),
                     EXTRACT_FUNC_ID_FROM_GLOBAL_ID (val2));
          fprintf (dump_file, "Transformation on insn\n");
          print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
          fprintf (dump_file, "=>\n");
          print_gimple_stmt (dump_file, modify2, 0, TDF_SLIM);
          fprintf (dump_file, "hist->count "HOST_WIDEST_INT_PRINT_DEC
                   " hist->all "HOST_WIDEST_INT_PRINT_DEC"\n", count2,
                   all - count1);
        }
    }

  return true;
}

/* Perform indirect call (STMT) to guarded direct function call
   transformation using value profile data.  */

static bool
gimple_ic_transform (gimple stmt)
{
  histogram_value histogram;
  tree callee;

  if (gimple_code (stmt) != GIMPLE_CALL)
    return false;

  callee = gimple_call_fn (stmt);

  if (TREE_CODE (callee) == FUNCTION_DECL)
    return false;

  histogram = gimple_histogram_value_of_type (cfun, stmt, HIST_TYPE_INDIR_CALL);
  if (!histogram)
    {
      histogram = gimple_histogram_value_of_type (cfun, stmt,
                                                  HIST_TYPE_INDIR_CALL_TOPN);
      if (!histogram)
        return false;
    }

  if (histogram->type == HIST_TYPE_INDIR_CALL)
    return gimple_ic_transform_single_targ (stmt, histogram);
  else
    return gimple_ic_transform_mult_targ (stmt, histogram);
}

/* Return true if the stringop CALL with FNDECL shall be profiled.  If
   SIZE_ARG is not null, it will be the argument index for the size of
   the string operation. 
*/
static bool
interesting_stringop_to_profile_p (tree fndecl, gimple call, int *size_arg)
{
  enum built_in_function fcode = DECL_FUNCTION_CODE (fndecl);

  /* XXX: Disable stringop collection with reuse distance instrumentation
     or optimization.  Otherwise we end up with hard to correct profile
     mismatches for functions where reuse distance-based transformation are
     made.  We see a number of "memcpy" at instrumentation time and a different
     number of "memcpy" at profile use time.  */
  if (flag_profile_reusedist || flag_optimize_locality)
    return false;

  if (fcode != BUILT_IN_MEMCPY && fcode != BUILT_IN_MEMPCPY
      && fcode != BUILT_IN_MEMSET && fcode != BUILT_IN_BZERO)
    return false;

  switch (fcode)
    {
     case BUILT_IN_MEMCPY:
     case BUILT_IN_MEMPCPY:
       if (size_arg)
         *size_arg = 2;
       return validate_gimple_arglist (call, POINTER_TYPE, POINTER_TYPE,
				       INTEGER_TYPE, VOID_TYPE);
     case BUILT_IN_MEMSET:
       if (size_arg)
         *size_arg = 2;
       return validate_gimple_arglist (call, POINTER_TYPE, INTEGER_TYPE,
				      INTEGER_TYPE, VOID_TYPE);
     case BUILT_IN_BZERO:
       if (size_arg)
         *size_arg = 1;
       return validate_gimple_arglist (call, POINTER_TYPE, INTEGER_TYPE,
				       VOID_TYPE);
     default:
       gcc_unreachable ();
    }
}

/* Convert   stringop (..., size)
   into 
   if (size == VALUE)
     stringop (...., VALUE);
   else
     stringop (...., size);
   assuming constant propagation of VALUE will happen later.
*/
static void
gimple_stringop_fixed_value (gimple stmt, tree value, int prob, gcov_type count,
			     gcov_type all)
{
  gimple stmt1, stmt2, stmt3;
  tree tmp1, tmpv;
  gimple bb1end, bb2end;
  basic_block bb, bb2, bb3, bb4;
  edge e12, e13, e23, e24, e34;
  gimple_stmt_iterator gsi;
  tree fndecl;
  tree blck_size;
  tree optype;
  int region;
  int size_arg;

  fndecl = gimple_call_fndecl (stmt);
  if (!interesting_stringop_to_profile_p (fndecl, stmt, &size_arg))
    gcc_unreachable();
  blck_size = gimple_call_arg (stmt, size_arg);
  optype = TREE_TYPE (blck_size);

  bb = gimple_bb (stmt);
  gsi = gsi_for_stmt (stmt);

  if (gsi_end_p (gsi))
    {
      edge_iterator ei;
      for (ei = ei_start (bb->succs); (e34 = ei_safe_edge (ei)); )
	if (!(e34->flags & EDGE_ABNORMAL))
	  break;
    }
  else
    {
      e34 = split_block (bb, stmt);
      gsi = gsi_for_stmt (stmt);
    }
  bb4 = e34->dest;

  tmpv = create_tmp_var (optype, "PROF");
  tmp1 = create_tmp_var (optype, "PROF");
  stmt1 = gimple_build_assign (tmpv, fold_convert (optype, value));
  stmt2 = gimple_build_assign (tmp1, blck_size);
  stmt3 = gimple_build_cond (NE_EXPR, tmp1, tmpv, NULL_TREE, NULL_TREE);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt2, GSI_SAME_STMT);
  gsi_insert_before (&gsi, stmt3, GSI_SAME_STMT);
  bb1end = stmt3;

  stmt1 = gimple_copy (stmt);
  gimple_call_set_arg (stmt1, size_arg, value);
  gsi_insert_before (&gsi, stmt1, GSI_SAME_STMT);
  region = lookup_stmt_eh_region (stmt);
  if (region >= 0)
    add_stmt_to_eh_region (stmt1, region);
  bb2end = stmt1;

  /* Fix CFG. */
  /* Edge e23 connects bb2 to bb3, etc. */
  e12 = split_block (bb, bb1end);
  bb2 = e12->dest;
  bb2->count = count;
  e23 = split_block (bb2, bb2end);
  bb3 = e23->dest;
  bb3->count = all - count;

  e12->flags &= ~EDGE_FALLTHRU;
  e12->flags |= EDGE_FALSE_VALUE;
  e12->probability = prob;
  e12->count = count;

  e13 = make_edge (bb, bb3, EDGE_TRUE_VALUE);
  e13->probability = REG_BR_PROB_BASE - prob;
  e13->count = all - count;

  remove_edge (e23);
  
  e24 = make_edge (bb2, bb4, EDGE_FALLTHRU);
  e24->probability = REG_BR_PROB_BASE;
  e24->count = count;

  e34->probability = REG_BR_PROB_BASE;
  e34->count = all - count;
}

/* Find values inside STMT for that we want to measure histograms for
   division/modulo optimization.  */
static bool
gimple_stringops_transform (gimple_stmt_iterator *gsi)
{
  gimple stmt = gsi_stmt (*gsi);
  tree fndecl;
  tree blck_size;
  enum built_in_function fcode;
  histogram_value histogram;
  gcov_type count, all, val;
  tree value;
  tree dest, src;
  unsigned int dest_align, src_align;
  gcov_type prob;
  tree tree_val;
  int size_arg;

  if (gimple_code (stmt) != GIMPLE_CALL)
    return false;
  fndecl = gimple_call_fndecl (stmt);
  if (!fndecl)
    return false;
  fcode = DECL_FUNCTION_CODE (fndecl);
  if (!interesting_stringop_to_profile_p (fndecl, stmt, &size_arg))
    return false;

  blck_size = gimple_call_arg (stmt, size_arg);
  if (TREE_CODE (blck_size) == INTEGER_CST)
    return false;

  histogram = gimple_histogram_value_of_type (cfun, stmt, HIST_TYPE_SINGLE_VALUE);
  if (!histogram)
    return false;
  value = histogram->hvalue.value;
  val = histogram->hvalue.counters[0];
  count = histogram->hvalue.counters[1];
  all = histogram->hvalue.counters[2];
  gimple_remove_histogram_value (cfun, stmt, histogram);
  /* We require that count is at least half of all; this means
     that for the transformation to fire the value must be constant
     at least 80% of time.  */
  if ((6 * count / 5) < all || optimize_bb_for_size_p (gimple_bb (stmt)))
    return false;
  if (check_counter (stmt, "value", &count, &all, gimple_bb (stmt)->count))
    return false;
  if (all > 0)
    prob = (count * REG_BR_PROB_BASE + all / 2) / all;
  else
    prob = 0;
  dest = gimple_call_arg (stmt, 0);
  dest_align = get_pointer_alignment (dest, BIGGEST_ALIGNMENT);
  switch (fcode)
    {
    case BUILT_IN_MEMCPY:
    case BUILT_IN_MEMPCPY:
      src = gimple_call_arg (stmt, 1);
      src_align = get_pointer_alignment (src, BIGGEST_ALIGNMENT);
      if (!can_move_by_pieces (val, MIN (dest_align, src_align)))
	return false;
      break;
    case BUILT_IN_MEMSET:
      if (!can_store_by_pieces (val, builtin_memset_read_str,
				gimple_call_arg (stmt, 1),
				dest_align, true))
	return false;
      break;
    case BUILT_IN_BZERO:
      if (!can_store_by_pieces (val, builtin_memset_read_str,
				integer_zero_node,
				dest_align, true))
	return false;
      break;
    default:
      gcc_unreachable ();
    }
  tree_val = build_int_cst_wide (get_gcov_type (),
				 (unsigned HOST_WIDE_INT) val,
				 val >> (HOST_BITS_PER_WIDE_INT - 1) >> 1);
  if (dump_file)
    {
      fprintf (dump_file, "Single value %i stringop transformation on ",
	       (int)val);
      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
    }
  gimple_stringop_fixed_value (stmt, tree_val, prob, count, all);
  
  return true;
}

void
stringop_block_profile (gimple stmt, unsigned int *expected_align,
			HOST_WIDE_INT *expected_size)
{
  histogram_value histogram;
  histogram = gimple_histogram_value_of_type (cfun, stmt, HIST_TYPE_AVERAGE);
  if (!histogram)
    *expected_size = -1;
  else if (!histogram->hvalue.counters[1])
    {
      *expected_size = -1;
      gimple_remove_histogram_value (cfun, stmt, histogram);
    }
  else
    {
      gcov_type size;
      size = ((histogram->hvalue.counters[0]
	      + histogram->hvalue.counters[1] / 2)
	       / histogram->hvalue.counters[1]);
      /* Even if we can hold bigger value in SIZE, INT_MAX
	 is safe "infinity" for code generation strategies.  */
      if (size > INT_MAX)
	size = INT_MAX;
      *expected_size = size;
      gimple_remove_histogram_value (cfun, stmt, histogram);
    }
  histogram = gimple_histogram_value_of_type (cfun, stmt, HIST_TYPE_IOR);
  if (!histogram)
    *expected_align = 0;
  else if (!histogram->hvalue.counters[0])
    {
      gimple_remove_histogram_value (cfun, stmt, histogram);
      *expected_align = 0;
    }
  else
    {
      gcov_type count;
      int alignment;

      count = histogram->hvalue.counters[0];
      alignment = 1;
      while (!(count & alignment)
	     && (alignment * 2 * BITS_PER_UNIT))
	alignment <<= 1;
      *expected_align = alignment * BITS_PER_UNIT;
      gimple_remove_histogram_value (cfun, stmt, histogram);
    }
}



/* Find log,exp,pow,squrt calls and profile arguments.  */
static void
gimple_math_call_to_profile (gimple stmt, histogram_values *values)
{
  /*   histogram_value hist; */
  tree fndecl;
  tree arg1;
  enum ffvpt_math_functions math_fun;

  if (gimple_code (stmt) != GIMPLE_CALL)
    return;

  /* Hopefully the math function */
  fndecl = gimple_call_fndecl (stmt);
  if (fndecl == NULL)
    return;

  /* Look for amd_exp, amd_log, amd_pow*/
  math_fun = get_ffvpt_math_function (stmt, fndecl);
  if (math_fun != FFVPT_UNSUPPORTED_FUN)
    {
      if (math_fun == FFVPT_POW_FUN || math_fun == FFVPT_AMD_POW_FUN)
        arg1 = gimple_call_arg (stmt, 1);
      else
        arg1 = gimple_call_arg (stmt, 0);
      if (dump_file)
        {
          fprintf (dump_file, "Add profiling for call to %s in %s\n",
                   lang_hooks.decl_printable_name (fndecl, 1),
                   current_function_name ());
        }
      VEC_reserve (histogram_value, heap, *values, 3);
      VEC_quick_push (histogram_value, *values,
                      gimple_alloc_histogram_value (cfun,
                                                    HIST_TYPE_SINGLE_FLOAT_VALUE,
                                                    stmt, arg1));
    }
  return;
}



struct value_prof_hooks {
  /* Find list of values for which we want to measure histograms.  */
  void (*find_values_to_profile) (histogram_values *);

  /* Identify and exploit properties of values that are hard to analyze
     statically.  See value-prof.c for more detail.  */
  bool (*value_profile_transformations) (void);  
};

/* Find values inside STMT for that we want to measure histograms for
   division/modulo optimization.  */
static void
gimple_divmod_values_to_profile (gimple stmt, histogram_values *values)
{
  tree lhs, divisor, op0, type;
  histogram_value hist;

  if (gimple_code (stmt) != GIMPLE_ASSIGN)
    return;

  lhs = gimple_assign_lhs (stmt);
  type = TREE_TYPE (lhs);
  if (!INTEGRAL_TYPE_P (type))
    return;

  switch (gimple_assign_rhs_code (stmt))
    {
    case TRUNC_DIV_EXPR:
    case TRUNC_MOD_EXPR:
      divisor = gimple_assign_rhs2 (stmt);
      op0 = gimple_assign_rhs1 (stmt);

      VEC_reserve (histogram_value, heap, *values, 3);

      if (is_gimple_reg (divisor))
	/* Check for the case where the divisor is the same value most
	   of the time.  */
	VEC_quick_push (histogram_value, *values,
			gimple_alloc_histogram_value (cfun,
						      HIST_TYPE_SINGLE_VALUE,
						      stmt, divisor));

      /* For mod, check whether it is not often a noop (or replaceable by
	 a few subtractions).  */
      if (gimple_assign_rhs_code (stmt) == TRUNC_MOD_EXPR
	  && TYPE_UNSIGNED (type))
	{
          tree val;
          /* Check for a special case where the divisor is power of 2.  */
	  VEC_quick_push (histogram_value, *values,
			  gimple_alloc_histogram_value (cfun, HIST_TYPE_POW2,
							stmt, divisor));

	  val = build2 (TRUNC_DIV_EXPR, type, op0, divisor);
	  hist = gimple_alloc_histogram_value (cfun, HIST_TYPE_INTERVAL,
					       stmt, val);
	  hist->hdata.intvl.int_start = 0;
	  hist->hdata.intvl.steps = 2;
	  VEC_quick_push (histogram_value, *values, hist);
	}
      return;

    default:
      return;
    }
}

/* From sample profiles, find values inside STMT for that we want to measure
   histograms for indirect-call optimization.  */
static histogram_value
gimple_sample_indirect_call (gimple stmt, struct sample_hist *values, int count)
{
  tree callee;
  int i, total = 0;
  int actual_count = 0;
  histogram_value hist;

  if (gimple_code (stmt) != GIMPLE_CALL
      || gimple_call_fndecl (stmt) != NULL_TREE)
    return NULL;

  callee = gimple_call_fn (stmt);

  for (i = 0; i < count; i++) {
    if (values[i].type == CALL_HIST) break;
  }

  if (i == count) return NULL;

  hist = gimple_alloc_histogram_value (cfun, HIST_TYPE_INDIR_CALL_TOPN,
                                       stmt, callee);
  hist->n_counters = (GCOV_ICALL_TOPN_VAL << 2) + 1;
  hist->hvalue.counters =  XNEWVEC (gcov_type, hist->n_counters);
  gimple_add_histogram_value (cfun, stmt, hist);


  for (i = 0; i < count; i++) {
    if (values[i].type == CALL_HIST) {
      total += values[i].count;
      if (actual_count < 2) {
        hist->hvalue.counters[actual_count * 2 + 1] =
            (unsigned long long) values[i].value.func_name;
        hist->hvalue.counters[actual_count * 2 + 2] = values[i].count;
        actual_count ++;
      }
    }
  }

  hist->hvalue.counters[0] = total;

  if (actual_count == 1) {
    hist->hvalue.counters[3] = 0;
    hist->hvalue.counters[4] = 0;
  }
  return hist;
}

/* From sample profiles, find values inside STMT for that we want to measure
   histograms for stringop optimization.  */
static histogram_value
gimple_sample_stringop (gimple stmt, struct sample_hist *values, int count)
{
  int i, total = 0;
  int actual_count = 0;
  tree fndecl;
  tree blck_size;
  enum built_in_function fcode;
  int size_arg;
  histogram_value hist;

  if (gimple_code (stmt) != GIMPLE_CALL)
    return NULL;
  fndecl = gimple_call_fndecl (stmt);
  if (!fndecl)
    return NULL;
  fcode = DECL_FUNCTION_CODE (fndecl);

  if (!interesting_stringop_to_profile_p (fndecl, stmt, &size_arg))
    return NULL;

  blck_size = gimple_call_arg (stmt, size_arg);

  if (TREE_CODE (blck_size) == INTEGER_CST)
    return NULL;

  for (i = 0; i < count; i++) {
    if (values[i].type == STRINGOP_HIST) break;
  }

  if (i == count) return NULL;

  hist = gimple_alloc_histogram_value (cfun, HIST_TYPE_SINGLE_VALUE,
                                       stmt, blck_size);
  hist->n_counters = 3;
  hist->hvalue.counters =  XNEWVEC (gcov_type, hist->n_counters);
  gimple_add_histogram_value (cfun, stmt, hist);

  for (i = 0; i < count; i++) {
    if (values[i].type == STRINGOP_HIST) {
      total += values[i].count;
      if (actual_count < 1) {
        hist->hvalue.counters[0] = values[i].value.value;
        hist->hvalue.counters[1] = values[i].count;
        actual_count ++;
      }
    }
  }
  hist->hvalue.counters[2] = total;
  return hist;
}

/* From sample profiles, find values inside STMT for that we want to measure
   histograms for div/mod optimization.  */
static histogram_value
gimple_sample_divmod (gimple stmt, struct sample_hist *values, int count)
{
  int i, total = 0;
  int actual_count = 0;
  tree lhs, divisor, type;
  histogram_value hist;

  if (gimple_code (stmt) != GIMPLE_ASSIGN)
    return NULL;;

  lhs = gimple_assign_lhs (stmt);
  type = TREE_TYPE (lhs);
  if (!INTEGRAL_TYPE_P (type))
    return NULL;;

  if (gimple_assign_rhs_code (stmt) != TRUNC_DIV_EXPR &&
      gimple_assign_rhs_code (stmt) != TRUNC_MOD_EXPR)
    return NULL;

  for (i = 0; i < count; i++) {
    if (values[i].type == DIVMOD_HIST) break;
  }

  if ( i == count) return NULL;

  divisor = gimple_assign_rhs2 (stmt);

  hist = gimple_alloc_histogram_value (cfun, HIST_TYPE_SINGLE_VALUE,
                                       stmt, divisor);
  hist->n_counters = 3;
  hist->hvalue.counters =  XNEWVEC (gcov_type, hist->n_counters);
  gimple_add_histogram_value (cfun, stmt, hist);

  for (i = 0; i < count; i++) {
    if (values[i].type == DIVMOD_HIST) {
      total += values[i].count;
      if (actual_count < 1) {
        hist->hvalue.counters[0] = values[i].value.value;
        hist->hvalue.counters[1] = values[i].count;
        actual_count ++;
      }
    }
  }
  hist->hvalue.counters[2] = total;
  return hist;
}

/* From sample profiles, find values inside STMT for that we want to measure
   histograms and adds them to list VALUES.  */
void gimple_sample_vpt (gimple stmt, struct sample_hist *v, int count)
{
  gimple_sample_indirect_call (stmt, v, count);
  gimple_sample_stringop (stmt, v, count);
  gimple_sample_divmod (stmt, v, count);
}

/* Find calls inside STMT for that we want to measure histograms for 
   indirect/virtual call optimization. */ 

static void
gimple_indirect_call_to_profile (gimple stmt, histogram_values *values)
{
  tree callee;

  if (gimple_code (stmt) != GIMPLE_CALL
      || gimple_call_fndecl (stmt) != NULL_TREE)
    return;

  callee = gimple_call_fn (stmt);

  VEC_reserve (histogram_value, heap, *values, 3);

  if (flag_dyn_ipa)
    VEC_quick_push (histogram_value, *values, 
		    gimple_alloc_histogram_value (cfun, HIST_TYPE_INDIR_CALL_TOPN,
						  stmt, callee));
  else
    VEC_quick_push (histogram_value, *values, 
		    gimple_alloc_histogram_value (cfun, HIST_TYPE_INDIR_CALL,
						  stmt, callee));

  return;
}

/* Find values inside STMT for that we want to measure histograms for
   string operations.  */
static void
gimple_stringops_values_to_profile (gimple stmt, histogram_values *values)
{
  tree fndecl;
  tree blck_size;
  tree dest;
  enum built_in_function fcode;
  int size_arg;

  if (gimple_code (stmt) != GIMPLE_CALL)
    return;
  fndecl = gimple_call_fndecl (stmt);
  if (!fndecl)
    return;
  fcode = DECL_FUNCTION_CODE (fndecl);

  if (!interesting_stringop_to_profile_p (fndecl, stmt, &size_arg))
    return;

  dest = gimple_call_arg (stmt, 0);
  blck_size = gimple_call_arg (stmt, size_arg);

  if (TREE_CODE (blck_size) != INTEGER_CST)
    {
      VEC_safe_push (histogram_value, heap, *values,
		     gimple_alloc_histogram_value (cfun, HIST_TYPE_SINGLE_VALUE,
						   stmt, blck_size));
      VEC_safe_push (histogram_value, heap, *values,
		     gimple_alloc_histogram_value (cfun, HIST_TYPE_AVERAGE,
						   stmt, blck_size));
    }
  if (TREE_CODE (blck_size) != INTEGER_CST)
    VEC_safe_push (histogram_value, heap, *values,
		   gimple_alloc_histogram_value (cfun, HIST_TYPE_IOR,
						 stmt, dest));
}

/* Find values inside STMT for that we want to measure histograms and adds
   them to list VALUES.  */

static void
gimple_values_to_profile (gimple stmt, histogram_values *values)
{
  if (flag_value_profile_transformations)
    {
      gimple_divmod_values_to_profile (stmt, values);
      gimple_stringops_values_to_profile (stmt, values);
      gimple_indirect_call_to_profile (stmt, values);
      if (flag_float_value_profile_transformations)
        gimple_math_call_to_profile (stmt, values);
    }
}

static void
gimple_find_values_to_profile (histogram_values *values)
{
  basic_block bb;
  gimple_stmt_iterator gsi;
  unsigned i;
  histogram_value hist = NULL;

  *values = NULL;
  FOR_EACH_BB (bb)
    for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
      gimple_values_to_profile (gsi_stmt (gsi), values);

  for (i = 0; VEC_iterate (histogram_value, *values, i, hist); i++)
    {
      switch (hist->type)
        {
	case HIST_TYPE_INTERVAL:
	  hist->n_counters = hist->hdata.intvl.steps + 2;
	  break;

	case HIST_TYPE_POW2:
	  hist->n_counters = 2;
	  break;

	case HIST_TYPE_SINGLE_VALUE:
	  hist->n_counters = 3;
	  break;

	case HIST_TYPE_SINGLE_FLOAT_VALUE:
	  hist->n_counters = 3;
	  break;

	case HIST_TYPE_CONST_DELTA:
	  hist->n_counters = 4;
	  break;

 	case HIST_TYPE_INDIR_CALL:
	  hist->n_counters = 3;
	  break;

	case HIST_TYPE_AVERAGE:
	  hist->n_counters = 2;
	  break;

	case HIST_TYPE_IOR:
	  hist->n_counters = 1;
	  break;

 	case HIST_TYPE_INDIR_CALL_TOPN:
          hist->n_counters = (GCOV_ICALL_TOPN_VAL << 2) + 1;
	  break;

	default:
	  gcc_unreachable ();
	}
      if (dump_file)
        {
	  fprintf (dump_file, "Stmt ");
          print_gimple_stmt (dump_file, hist->hvalue.stmt, 0, TDF_SLIM);
	  dump_histogram_value (dump_file, hist);
        }
    }
}

static struct value_prof_hooks gimple_value_prof_hooks = {
  gimple_find_values_to_profile,
  gimple_value_profile_transformations
};

void
gimple_register_value_prof_hooks (void)
{
  gcc_assert (current_ir_type () == IR_GIMPLE);
  value_prof_hooks = &gimple_value_prof_hooks;
}

/* IR-independent entry points.  */
void
find_values_to_profile (histogram_values *values)
{
  (value_prof_hooks->find_values_to_profile) (values);
}

bool
value_profile_transformations (void)
{
  return (value_prof_hooks->value_profile_transformations) ();
}

