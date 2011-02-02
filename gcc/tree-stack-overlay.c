/* A pass for coalescing stack variables.

   Copyright (C) 2010
   Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "ggc.h"
#include "tm.h"
#include "tree.h"
#include "tm_p.h"
#include "basic-block.h"
#include "function.h"
#include "expr.h"
#include "langhooks.h"
#include "tree-flow.h"
#include "timevar.h"
#include "tree-dump.h"
#include "tree-pass.h"
#include "except.h"
#include "flags.h"
#include "diagnostic.h"
#include "toplev.h"
#include "debug.h"
#include "params.h"
#include "target.h"
#include "tree-stack-overlay.h"
#include "vec.h"


/* Based on the stack layout phase in cfgexpand. Creates new union
   types with variables that can share stack slots as fields. During
   RTL generation, all fields of the union arer assigned to the same
   stack slot.  */

#define EOC  (-1)

/* This structure holds data relevant to one variable that will be
   placed in a stack slot.  */
struct stack_var
{
  /* The Variable.  */
  tree decl;


  /* Initially, the size of the variable.  Later, the size of the partition,
     if this variable becomes it's partition's representative.  */
  HOST_WIDE_INT size;

  /* The partition representative.  */
  int representative;

  /* The next stack variable in the partition, or EOC.  */
  int next;

  /* The numbers of conflicting stack variables.  */
  bitmap conflicts;

  /* A new union type containing all variables in the partition. NULL if the
     partition is singleton. */
  tree union_decl;

  /* The field corresponding to this declaration in the created union */
  tree field_decl;
};

/* This struct maps a VAR_DECL to a vector of DECLs. */
struct overlay_decl_mapping GTY(())
{
  tree decl;
  VEC(tree,gc) *value;
};


/* We have an array of such objects while deciding allocation.  */
static struct stack_var *stack_vars;
static int stack_vars_alloc;
static int stack_vars_num;

/* Map between var_decl to field_decl inside a union type. */
static htab_t decl_field_map = NULL;

/* Store newly synthesized union variables in union_vars. */
static tree union_vars = NULL_TREE;

/* An array of indices such that stack_vars[stack_vars_sorted[i]].size
   is non-decreasing.  */
static int *stack_vars_sorted;

/* Make the decls associated with luid's X and Y conflict.  */

static void
add_stack_var_conflict (size_t x, size_t y)
{
  struct stack_var *a = &stack_vars[x];
  struct stack_var *b = &stack_vars[y];
  if (!a->conflicts)
    a->conflicts = BITMAP_ALLOC (NULL);
  if (!b->conflicts)
    b->conflicts = BITMAP_ALLOC (NULL);
  bitmap_set_bit (a->conflicts, y);
  bitmap_set_bit (b->conflicts, x);
}

/* Check whether the decls associated with luid's X and Y conflict.  */

static bool
stack_var_conflict_p (size_t x, size_t y)
{
  struct stack_var *a = &stack_vars[x];
  struct stack_var *b = &stack_vars[y];
  if (!a->conflicts || !b->conflicts)
    return false;
  return bitmap_bit_p (a->conflicts, y);
}

/* Returns true if TYPE is or contains a union type.  */

static bool
aggregate_contains_union_type (tree type)
{
  tree field;

  if (TREE_CODE (type) == UNION_TYPE
      || TREE_CODE (type) == QUAL_UNION_TYPE)
    return true;
  if (TREE_CODE (type) == ARRAY_TYPE)
    return aggregate_contains_union_type (TREE_TYPE (type));
  if (TREE_CODE (type) != RECORD_TYPE)
    return false;

  for (field = TYPE_FIELDS (type); field; field = TREE_CHAIN (field))
    if (TREE_CODE (field) == FIELD_DECL)
      if (aggregate_contains_union_type (TREE_TYPE (field)))
        return true;

  return false;
}

/* A subroutine of execute_stack_overlay.  If two variables X and Y have
   alias sets that do not conflict, then do add a conflict for these
   variable in the interference graph.  We also need to make sure to add
   conflicts for union containing structures.  Else RTL alias analysis
   comes along and due to type based aliasing rules decides that for two
   overlapping union temporaries { short s; int i; } accesses to the same
   mem through different types may not alias and happily reorders stores
   across life-time boundaries of the temporaries (See PR25654).
   We also have to mind MEM_IN_STRUCT_P and MEM_SCALAR_P.  */

static void
add_alias_set_conflicts (void)
{
  size_t i, j, n = stack_vars_num;

  for (i = 0; i < n; ++i)
    {
      tree type_i = TREE_TYPE (stack_vars[i].decl);
      bool aggr_i = AGGREGATE_TYPE_P (type_i);
      bool contains_union;

      contains_union = aggregate_contains_union_type (type_i);
      for (j = 0; j < i; ++j)
        {
          tree type_j = TREE_TYPE (stack_vars[j].decl);
          bool aggr_j = AGGREGATE_TYPE_P (type_j);
          if (aggr_i != aggr_j
              /* Either the objects conflict by means of type based
                 aliasing rules, or we need to add a conflict.  */
              || !objects_must_conflict_p (type_i, type_j)
              /* In case the types do not conflict ensure that access
                 to elements will conflict.  In case of unions we have
                 to be careful as type based aliasing rules may say
                 access to the same memory does not conflict.  So play
                 safe and add a conflict in this case.  */
              || (contains_union && flag_strict_aliasing))
            add_stack_var_conflict (i, j);
        }
    }
}

/* Examine TYPE and determine a bit mask of the following features.  */

#define SPCT_HAS_LARGE_CHAR_ARRAY	1
#define SPCT_HAS_SMALL_CHAR_ARRAY	2
#define SPCT_HAS_ARRAY			4
#define SPCT_HAS_AGGREGATE		8

static unsigned int
stack_protect_classify_type (tree type)
{
  unsigned int ret = 0;
  tree t;

  switch (TREE_CODE (type))
    {
    case ARRAY_TYPE:
      t = TYPE_MAIN_VARIANT (TREE_TYPE (type));
      if (t == char_type_node
          || t == signed_char_type_node
          || t == unsigned_char_type_node)
        {
          unsigned HOST_WIDE_INT max = PARAM_VALUE (PARAM_SSP_BUFFER_SIZE);
          unsigned HOST_WIDE_INT len;

          if (!TYPE_SIZE_UNIT (type)
              || !host_integerp (TYPE_SIZE_UNIT (type), 1))
            len = max;
          else
            len = tree_low_cst (TYPE_SIZE_UNIT (type), 1);

          if (len < max)
            ret = SPCT_HAS_SMALL_CHAR_ARRAY | SPCT_HAS_ARRAY;
          else
            ret = SPCT_HAS_LARGE_CHAR_ARRAY | SPCT_HAS_ARRAY;
        }
      else
        ret = SPCT_HAS_ARRAY;
      break;

    case UNION_TYPE:
    case QUAL_UNION_TYPE:
    case RECORD_TYPE:
      ret = SPCT_HAS_AGGREGATE;
      for (t = TYPE_FIELDS (type); t ; t = TREE_CHAIN (t))
        if (TREE_CODE (t) == FIELD_DECL)
          ret |= stack_protect_classify_type (TREE_TYPE (t));
      break;

    default:
      break;
    }

  return ret;
}

/* Return nonzero if DECL should be segregated into the "vulnerable" upper
   part of the local stack frame.  Remember if we ever return nonzero for
   any variable in this function.  The return value is the phase number in
   which the variable should be allocated.  */

static int
stack_protect_decl_phase (tree decl)
{
  unsigned int bits = stack_protect_classify_type (TREE_TYPE (decl));
  int ret = 0;

  if (flag_stack_protect == 2)
    {
      if ((bits & (SPCT_HAS_SMALL_CHAR_ARRAY | SPCT_HAS_LARGE_CHAR_ARRAY))
          && !(bits & SPCT_HAS_AGGREGATE))
        ret = 1;
      else if (bits & SPCT_HAS_ARRAY)
        ret = 2;
    }
  else
    ret = (bits & SPCT_HAS_LARGE_CHAR_ARRAY) != 0;

  return ret;
}

/* Ensure that variables in different stack protection phases conflict
   so that they are not merged and share the same stack slot.  */

static void
add_stack_protection_conflicts (void)
{
  size_t i, j, n = stack_vars_num;
  unsigned char *phase;

  phase = XNEWVEC (unsigned char, n);
  for (i = 0; i < n; ++i)
    phase[i] = stack_protect_decl_phase (stack_vars[i].decl);

  for (i = 0; i < n; ++i)
    {
      unsigned char ph_i = phase[i];
      for (j = 0; j < i; ++j)
        if (ph_i != phase[j])
          add_stack_var_conflict (i, j);
    }

  XDELETEVEC (phase);
}

/* A subroutine of partition_stack_vars.  A comparison function for qsort,
   sorting an array of indices by the size of the object in descending
   order.  */

static int
stack_var_size_cmp (const void *a, const void *b)
{
  HOST_WIDE_INT sa = stack_vars[*(const int *)a].size;
  HOST_WIDE_INT sb = stack_vars[*(const int *)b].size;
  unsigned int uida = DECL_UID (stack_vars[*(const int *)a].decl);
  unsigned int uidb = DECL_UID (stack_vars[*(const int *)b].decl);

  if (sa > sb)
    return -1;
  if (sa < sb)
    return 1;
  /* For stack variables of the same size use the uid of the decl
     to make the sort stable.  */
  if (uida < uidb)
    return -1;
  if (uida > uidb)
    return 1;
  return 0;
}

/* A subroutine of partition_stack_vars.  B is the index of a stack var
   that is not merged with any other variable. A is the index of a stack
   var which is in a partition of one or more stack vars with A as the
   representative. Add B to the partition containing A, set B's representative
   to be A and extend A's conflict list with that of B's.  */

static void
union_stack_vars (int a, int b)
{
  struct stack_var *vb = &stack_vars[b];
  bitmap_iterator bi;
  unsigned u;


  /* Add B to A's partition.  */
  stack_vars[b].next = stack_vars[a].next;
  stack_vars[b].representative = a;
  stack_vars[a].next = b;

  /* Update the interference graph and merge the conflicts.  */
  if (vb->conflicts)
    {
      EXECUTE_IF_SET_IN_BITMAP (vb->conflicts, 0, u, bi)
        add_stack_var_conflict (a, u);
      BITMAP_FREE (vb->conflicts);
    }
}

/* A subroutine of execute_stack_overlay.  Binpack the variables into
   partitions constrained by the interference graph.  The overall
   algorithm used is as follows:

        Sort the objects by descending order of size.
        For each object A {
          S = size(A)
          O = 0
          loop {
            Look for the largest non-conflicting object B with size <= S.
            UNION (A, B)
          }
        }
*/

static void
partition_stack_vars (void)
{
  int si, sj, n = stack_vars_num;

  stack_vars_sorted = XNEWVEC (int, stack_vars_num);
  for (si = 0; si < n; ++si)
    stack_vars_sorted[si] = si;

  if (n == 1)
    return;

  /* Sorting in descending order prevents cases cases like this:
     sizeof(a) = 100, sizeof(b) = 100, sizeof(c) = 1, c conflicts with a.
     If variables are considered in ascending order, c and b would be
     merged resulting in 200 bytes stack frame size. Sorting in descending
     order results in a and b being merged, resulting in 101 bytes stack
     size.  */
  qsort (stack_vars_sorted, n, sizeof (int), stack_var_size_cmp);

  for (si = 0; si < n; ++si)
    {
      int i = stack_vars_sorted[si];
      /* Ignore objects that aren't partition representatives. If we
         see a var that is not a partition representative, it must
         have been merged earlier.  */
      if (stack_vars[i].representative != i)
        continue;

      for (sj = si + 1; sj < n; sj++)
        {
          int j = stack_vars_sorted[sj];

          /* Ignore objects that aren't partition representatives.  */
          if (stack_vars[j].representative != j)
            continue;

          /* Ignore conflicting objects.  */
          if (stack_var_conflict_p (i, j))
            continue;

          /* UNION the two objects.  */
          union_stack_vars (i, j);
        }
    }
}

/* A debugging aid for execute_stack_overlay. Dump the generated partitions. */

static void
dump_stack_var_partition (void)
{
  int si, i, j, n = stack_vars_num;
  int part = 0;

  for (si = 0; si < n; ++si)
    {
      i = stack_vars_sorted[si];

      /* Skip variables that aren't partition representatives, for now.  */
      if (stack_vars[i].representative != i)
        continue;

      fprintf (dump_file, "Partition %d: size " HOST_WIDE_INT_PRINT_DEC
               " variables : ", part++, stack_vars[i].size);

      for (j = i; j != EOC; j = stack_vars[j].next)
        {
          fputc (' ', dump_file);
          print_generic_expr (dump_file, stack_vars[j].decl, dump_flags);
        }
        fputc ('\n', dump_file);
    }
  fprintf (dump_file, "Number of partitions = %d\n", part);
}

/* A subroutine of add_stack_vars_in_block. Identify variables that will be
   stack-allocated and add them to stack_vars array. */

static void
add_stack_var (tree var)
{
  if (TREE_CODE (var) != VAR_DECL
      || DECL_EXTERNAL (var)
      || DECL_HAS_VALUE_EXPR_P (var)
      || TREE_STATIC (var)
      || DECL_RTL_SET_P (var)
      || DECL_HARD_REGISTER (var)
      || use_register_for_decl (var)
      || (flag_float_store && FLOAT_TYPE_P (TREE_TYPE (var)))
      /* If a volatile shares a slot with a non-volatile, the
         union has to be marked volatile to prevent unsafe
         optimizations, preventing optimizations on the original
         non-volatile.  */
      || (TYPE_VOLATILE (TREE_TYPE (var))))
    return;

  /* Without optimization, *most* variables are allocated from the
     stack, which makes the quadratic problem large exactly when we
     want compilation to proceed as quickly as possible.  On the
     other hand, we don't want the function's stack frame size to
     get completely out of hand.  So we avoid adding scalars and
     "small" aggregates to the list at all.  */
  if (optimize == 0 && tree_low_cst (DECL_SIZE_UNIT (var), 1) < 32)
    return;

  if (stack_vars_num >= stack_vars_alloc)
    {
      if (stack_vars_alloc)
        stack_vars_alloc = stack_vars_alloc * 3 / 2;
      else
        stack_vars_alloc = 32;
      stack_vars
        = XRESIZEVEC (struct stack_var, stack_vars, stack_vars_alloc);
    }
  stack_vars[stack_vars_num].decl = var;
  stack_vars[stack_vars_num].size = tree_low_cst (DECL_SIZE_UNIT (var), 1);

  /* All variables are initially in their own partition.  */
  stack_vars[stack_vars_num].representative = stack_vars_num;
  stack_vars[stack_vars_num].next = EOC;

  /* All variables initially conflict with no other.  */
  stack_vars[stack_vars_num].conflicts = NULL;

  stack_vars[stack_vars_num].union_decl = NULL;
  stack_vars[stack_vars_num].field_decl = NULL;

  stack_vars_num++;
}


/* A subroutine of execute_stack_overlay.  Walk down through the BLOCK tree
   identifying stack variables that can possibly be coalesced.

   TOPLEVEL is true if this is the outermost BLOCK.  */

static void
add_stack_vars_in_block (tree block, bool toplevel)
{
  size_t i, j, old_sv_num, this_sv_num, new_sv_num;
  tree t;

  old_sv_num = toplevel ? 0 : stack_vars_num;

  /* Collect all stack vars at this level if this is not the outermost block.
     Since vartiables in the outermost block always conflict with everything
     there is no need to add them to stack_vars. */
  if (!toplevel)
    for (t = BLOCK_VARS (block); t ; t = TREE_CHAIN (t))
      if (TREE_USED (t))
        add_stack_var (t);

  this_sv_num = stack_vars_num;

  /* Recursively call the method in all SUBBLOCKS. */
  for (t = BLOCK_SUBBLOCKS (block); t ; t = BLOCK_CHAIN (t))
    add_stack_vars_in_block (t, false);

  /* Since we do not track exact variable lifetimes (which is not even
     possible for variables whose address escapes), we mirror the block
     tree in the interference graph.  Here we cause all variables at this
     level, and all sublevels, to conflict.  Do make certain that a
     variable conflicts with itself.  */
  if (old_sv_num < this_sv_num)
    {
      new_sv_num = stack_vars_num;

      for (i = old_sv_num; i < new_sv_num; ++i)
        for (j = i < this_sv_num ? i+1 : this_sv_num; j-- > old_sv_num ;)
          add_stack_var_conflict (i, j);
    }
}

/* A subroutine of init_stack_overlay.  Walk down through the BLOCK tree
   and clear TREE_USED on all local variables.  */

static void
clear_tree_used (tree block)
{
  tree t;

  for (t = BLOCK_VARS (block); t ; t = TREE_CHAIN (t))
    /* if (!TREE_STATIC (t) && !DECL_EXTERNAL (t)) */
      TREE_USED (t) = 0;

  for (t = BLOCK_SUBBLOCKS (block); t ; t = BLOCK_CHAIN (t))
    clear_tree_used (t);
}

/* Create a name "union."+i and returns a tree corresponding to that */
static inline tree
get_union_name (int i)
{
  char * new_name = NULL;
  ASM_FORMAT_PRIVATE_NAME(new_name, "union", i);
  return get_identifier (new_name);
}

/* Given an index into stack_vars, create field declarations corresponbding to
   each variable in the partition and link them together into a single tree. */
static tree
create_fields (int index, size_t *align)
{
  tree new_types = NULL_TREE;
  tree last = NULL_TREE;
  *align = 0;

  while (index != EOC)
    {
      tree decl = stack_vars[index].decl;
      tree name = DECL_NAME (decl);
      tree type = TREE_TYPE(decl);
      tree new_decl = build_decl (FIELD_DECL, name, type);
      if (*align < DECL_ALIGN (decl))
        *align = DECL_ALIGN (decl);
      stack_vars[index].field_decl = new_decl;
      if (!new_types)
        new_types = new_decl;
      else
        TREE_CHAIN (last) = new_decl;
      last = new_decl;
      index = stack_vars[index].next;
    }
  TREE_CHAIN (last) = NULL_TREE;
  return new_types;
}
/* This functions builds an union for the partition
   with representative stack_vars[i]. */

static tree
build_union_type (int i)
{
  tree attributes = NULL_TREE; /* Attributes??? */
  tree ref = 0;
  tree x;
  size_t align;
  tree fields = create_fields (i, &align);
  tree name = get_union_name (i);

  ref = make_node (UNION_TYPE);
  TYPE_SIZE (ref) = 0;
  decl_attributes (&ref, attributes, (int) ATTR_FLAG_TYPE_IN_PLACE);
  TYPE_PACKED (ref) = 0; /* Packing ??? */
  for (x = fields; x; x = TREE_CHAIN (x))
    {
      DECL_CONTEXT (x) = ref;
      DECL_PACKED (x) |= TYPE_PACKED (ref);
    }
  TYPE_FIELDS (ref) = fields;
  DECL_CONTEXT (TYPE_FIELDS (ref)) = ref;
  TYPE_NAME (ref) = name;
  layout_type (ref);
  TYPE_ALIGN (ref) = align;
  if (dump_file) {
    tree tmp;
    fprintf (dump_file, "Created  new type: \n ");
    print_generic_expr (dump_file, ref, dump_flags);
    fprintf (dump_file, "  {\n");
    tmp = fields;
    while (tmp)
      {
        tree field_type = TREE_TYPE (tmp);
        fprintf (dump_file, "  ");
        print_generic_expr (dump_file, field_type, dump_flags);
        fprintf (dump_file, " ");
        print_generic_expr (dump_file, tmp, dump_flags);
        fprintf (dump_file, ";\n");
        tmp = TREE_CHAIN (tmp);
      }
    fprintf (dump_file, "};\n\n");
  }
  return ref;
}

/* Set attributes for a newly created VAR_DECL */
static inline void
set_decl_attributes (tree new_decl)
{

  TREE_PUBLIC (new_decl) = 0;
  TREE_THIS_VOLATILE (new_decl) = 0;
  TREE_ADDRESSABLE (new_decl) = 1;
  DECL_TLS_MODEL (new_decl) = TLS_MODEL_NONE;
  /* Unset DECL_IGNORED_P to prevent this variable from being removed from
     BLOCK_VARS by remove_unused_locals */
  DECL_IGNORED_P (new_decl) = 0;
}

/* This function generates and returns new variable name based on
   ORIG_DECL name, combined with index I.
   The form of the new name is <orig_name>.<I> .  */

static tree
gen_var_name (unsigned HOST_WIDE_INT i)
{
  const char *old_name = "union";
  char *prefix;
  char *new_name;
  prefix = XALLOCAVEC (char, strlen (old_name) + 1);
  strcpy (prefix, old_name);
  ASM_FORMAT_PRIVATE_NAME (new_name, prefix, i);
  return get_identifier (new_name);
}
/* Create a new local variable of the given type */
static tree
create_new_var (tree type, size_t i)
{
  tree new_decl = NULL;
  tree new_name = gen_var_name (i);
  const char *name = IDENTIFIER_POINTER (new_name);
  new_decl = create_tmp_var (type, name); /* New var name??? */
  set_decl_attributes (new_decl);
  add_referenced_var (new_decl);
  get_var_ann (new_decl);
  TREE_CHAIN (new_decl) = union_vars;
  /* Do not emit any spurious uninitialized variable warning for
     the synthesized variable. */
  TREE_NO_WARNING (new_decl) = 1;
  union_vars = new_decl;
  return new_decl;
}

/* Build union VAR_DECLs for each partition in stack_vars */
static void
build_union_decls (void)
{
  int i;
  tree outer_block = DECL_INITIAL (current_function_decl);
  for (i = 0; i < stack_vars_num; i++)
    {
      if (stack_vars[i].next != EOC && stack_vars[i].representative == i)
        {
          tree new_type = build_union_type (i);
          tree new_decl;
          new_decl = create_new_var (new_type, i);
          stack_vars[i].union_decl = new_decl;
        }
    }
  BLOCK_VARS (outer_block) = chainon (BLOCK_VARS (outer_block), union_vars);

}

/* Hash function for overlay_decl_mapping */
static hashval_t
overlay_decl_mapping_hash (const void *x)
{
  return htab_hash_pointer (((const struct overlay_decl_mapping *)x)->decl);
}

/* Equality function for overlay_decl_mapping */
static int
overlay_decl_mapping_eq (const void *x, const void *y)
{
  return ((const struct overlay_decl_mapping *)x)->decl == (const_tree)y;
}

/* This function is a callback for traversal over decl_field_map
   hashtable. SLOT is a pointer to struct overlay_decl_mapping. This
   function frees memory allocated for  overlay_decl_mapping and pointed
   by *SLOT.  */

static int
free_decl_field_map_entry (void **slot, void *data ATTRIBUTE_UNUSED)
{
  struct overlay_decl_mapping *entry = (struct overlay_decl_mapping *)*slot;
  VEC_free (tree, gc, entry->value);
  ggc_free (entry);
  *slot = NULL;
  return 1;
}

/* Free decl_field_map hashtable.  */

static void
free_htab (htab_t table)
{
  if (table)
    htab_traverse (table, free_decl_field_map_entry, NULL);
  htab_delete (table);
}

static void
add_to_decl_map (htab_t decl_map, tree union_decl, tree original_decl)
{
  void **slot =
      htab_find_slot_with_hash (decl_map, union_decl,
                                htab_hash_pointer(union_decl), INSERT);
  struct overlay_decl_mapping *map_entry =
      (struct overlay_decl_mapping *)(*slot);
  if (map_entry == NULL)
    {
      map_entry = GGC_CNEW (struct overlay_decl_mapping);
      map_entry->decl = union_decl;
      *slot = map_entry;
    }
  VEC_safe_push (tree, gc, map_entry->value, original_decl);
}

/* Given the DECL of a synthesized variable, return a vector of original
   VAR_DECLs. */
VEC(tree,gc) *
get_original_stack_vars (tree union_decl)
{
  struct overlay_decl_mapping *entry;
  if (cfun->union_decl_list_map == NULL)
    return NULL;
  entry = (struct overlay_decl_mapping *)htab_find_with_hash
      (cfun->union_decl_list_map, union_decl, htab_hash_pointer(union_decl));
  if (entry == NULL)
    return NULL;
  return entry->value;
}

/* Traverse the stack_vars array and build the decl_field_map table for
   non-singleton partitions */
static void
build_decl_map (void)
{
  int i;
  tree new_field_decl;

  decl_field_map = htab_create (stack_vars_num, overlay_decl_mapping_hash,
                                overlay_decl_mapping_eq, NULL);
  cfun->union_decl_list_map =
      htab_create_ggc (stack_vars_num,overlay_decl_mapping_hash,
                   overlay_decl_mapping_eq, NULL);
  for (i = 0; i < stack_vars_num; i++)
    {
      tree field = stack_vars[i].field_decl;
      if (field != NULL)
        {
          tree field_type = TREE_TYPE (field);
          tree base = stack_vars[i].union_decl;
          if (base == NULL)
            base = stack_vars[stack_vars[i].representative].union_decl;
          new_field_decl =
              build3 (COMPONENT_REF, field_type, base, field, NULL_TREE);
          /* We need to retain the original variables to generate correct debug
             information. But since it does not have any uses it will be removed
             from REFERENCED_VARs which causes problems in alias analysis.
             Prevent the removal of the variable from the REFERENCED_VARs by
             setting TREE_ADDRESSABLE to 1. */
          TREE_ADDRESSABLE (stack_vars[i].decl) = 0;
          add_to_decl_map (decl_field_map, stack_vars[i].decl, new_field_decl);
          add_to_decl_map (cfun->union_decl_list_map, base, stack_vars[i].decl);
        }
    }
}
/* Callback function used to replace trees matching original stack variables
   with new union field declarations */
static tree
replace_vars_gimple_op (tree *tp, int *walk_subtrees, void *data)
{
  tree t = *tp;
  struct overlay_decl_mapping *tree_pair  =
      (struct overlay_decl_mapping *)htab_find_with_hash
      (decl_field_map, t, htab_hash_pointer(t));
  data = data;
  if (tree_pair != NULL)
    {
      *tp = VEC_index (tree, tree_pair->value, 0);
      *walk_subtrees = 0;
      if (data)
        {
          struct walk_stmt_info *wsi = (struct walk_stmt_info *)data;
          wsi->changed  = true;
        }
    }
  return NULL;

}

/* Returns true if DECL is replaced by a synthesized VAR_DECL.  */
static bool
replaced_var_decl (tree decl)
{
  struct overlay_decl_mapping *tree_pair  =
      (struct overlay_decl_mapping *)htab_find_with_hash
      (decl_field_map, decl, htab_hash_pointer(decl));
  return (tree_pair != NULL);
}

/* Replace all stack variables in a basic block */
static void
replace_vars_bb (basic_block bb)
{
  gimple_stmt_iterator gsi;
  struct walk_stmt_info wsi;
  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple stmt;
      stmt = gsi_stmt (gsi);
      wsi.pset = NULL;
      wsi.changed = false;
      if (gimple_code (stmt) != GIMPLE_LABEL)
        walk_gimple_op (stmt, replace_vars_gimple_op, &wsi);
      if (wsi.changed)
        update_stmt (stmt);
    }
  /* Traverse all PHI nodes in BB marking used operands.  */
  for (gsi = gsi_start_phis (bb); !gsi_end_p(gsi); gsi_next (&gsi))
    {
      use_operand_p arg_p;
      gimple phi;
      ssa_op_iter i;
      phi = gsi_stmt (gsi);
      FOR_EACH_PHI_ARG (arg_p, phi, i, SSA_OP_USE)
        {
          tree arg = USE_FROM_PTR (arg_p);
          wsi.changed = false;
          walk_tree (&arg, replace_vars_gimple_op, &wsi, NULL);
          if (wsi.changed)
            SET_USE (arg_p, arg);
        }
    }
}

/* Replace all stack variables in this function*/
static void
replace_vars (void)
{
  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
      replace_vars_bb (bb);
}

/* Prepare for stack overlay.  */
static void
init_stack_overlay (void)
{
  tree t;
  /* Clear TREE_USED on all variables associated with a block scope.  */
  clear_tree_used (DECL_INITIAL (current_function_decl));

  /* Set TREE_USED on all variables in the local_decls.  */
  for (t = cfun->local_decls; t; t = TREE_CHAIN (t))
    TREE_USED (TREE_VALUE (t)) = 1;
}

/* Free up stack variable graph data.  */
static void
fini_stack_overlay (void)
{
  size_t i, n = stack_vars_num;
  tree *cell;
  /* Remove replaced decls from local_decls.  */
  for (cell = &cfun->local_decls; *cell; )
    {
      tree var = TREE_VALUE (*cell);
      if (replaced_var_decl (var))
        {
          *cell = TREE_CHAIN(*cell);
          continue;
        }
      cell = &TREE_CHAIN (*cell);
    }

  for (i = 0; i < n; i++)
    BITMAP_FREE (stack_vars[i].conflicts);
  XDELETEVEC (stack_vars);
  XDELETEVEC (stack_vars_sorted);
  stack_vars = NULL;
  stack_vars_sorted = NULL;
  union_vars = NULL_TREE;
  stack_vars_alloc = stack_vars_num = 0;
  free_htab (decl_field_map);
  decl_field_map = NULL;
}

static unsigned int
execute_stack_overlay (void)
{
  tree outer_block = DECL_INITIAL (current_function_decl);


  init_stack_overlay ();

  /* At this point, all variables within the block tree with TREE_USED
     set are actually used by the optimized function.  Lay them out.  */
  add_stack_vars_in_block (outer_block, true);

  if (stack_vars_num > 0)
    {
      /* Due to the way alias sets work, no variables with non-conflicting
         alias sets may be assigned the same address.  Add conflicts to
         reflect this.  */
      add_alias_set_conflicts ();

      /* If stack protection is enabled, we don't share space between
         vulnerable data and non-vulnerable data.  */
      if (flag_stack_protect)
        add_stack_protection_conflicts ();

      /* Now that we have collected all stack variables, and have computed a
         minimal interference graph, attempt to save some stack space.  */
      partition_stack_vars ();
      if (dump_file)
        dump_stack_var_partition ();
      build_union_decls ();
      build_decl_map ();
      replace_vars ();
      fini_stack_overlay ();
    }


  return 0;
}

static bool
gate_stack_overlay (void)
{
  return flag_early_stack_alloc != 0;
}

struct gimple_opt_pass pass_stack_overlay=
{
 {
  GIMPLE_PASS,
  "stack-overlay",                      /* name */
  gate_stack_overlay,                   /* gate */
  execute_stack_overlay,                /* execute */
  NULL,                                 /* sub */
  NULL,                                 /* next */
  0,                                    /* static_pass_number */
  0,                                    /* tv_id */
  PROP_cfg,                             /* properties_required */
  0,                                    /* properties_provided */
  0,                                    /* properties_destroyed */
  0,                                    /* todo_flags_start */
  TODO_dump_func,                       /* todo_flags_finish */
 }
};

#include "gt-tree-stack-overlay.h"
