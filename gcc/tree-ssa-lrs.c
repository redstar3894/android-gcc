/* Live Range Shrinking Optimizations to reduce register pressure. 
   Copyright (C) 2009 Free Software Foundation, Inc.
   Contributed by Xinliang (David) Li davidxl@google.com

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
#include "tm.h"
#include "errors.h"
#include "ggc.h"
#include "tree.h"
#include "basic-block.h"
#include "diagnostic.h"
#include "tree-inline.h"
#include "tree-flow.h"
#include "gimple.h"
#include "tree-dump.h"
#include "timevar.h"
#include "tree-iterator.h"
#include "tree-pass.h"
#include "alloc-pool.h"
#include "vec.h"
#include "langhooks.h"
#include "pointer-set.h"
#include "cfgloop.h"
#include "flags.h"
#include "params.h"
#include "dbgcnt.h"
#include "tm_p.h"
#include "regs.h"
#include "ira-int.h"


/* Live range shrink transformation (LRS)

   High register pressures can result from many optimizations 
   aggressive function inlining, loop unrolling, loop fusion,
   strength reduction, expression reassociation, partitial 
   redundancy elimination, etc. The following example illustrates
   how expression reassociation can increase register pressure.

   x = ...
   y = ...
   a = x + y;
   u = ...
   b = a + u;
   v = ...
   c = b + v;
   w = ...
   d = c + w; (1)

 ==> After reasociation:

    x = ...
    y = ...
    u = ...
    v = ...
    w = ...
    a = y + x;
    b = a + v;
    c = b + u;
    d = c + w;

    Assuming only d is live across the statement (1), the max
    simultaneous live variables is 2 for the orignal code
    sequence (thus requires only 2 registers), while after
    reassocation, the number of regisers required is 5.

    The live range shrinking optimization tries to move uses
    as close as possible to its definitions if the number of
    overlapping live ranges can be reduced after the code motion.
    The techniques implemented in this pass include the following:

    1) Large expression reassociation: The objective of the 
       reassication is to enable more live range shrinking code
       motions which are otherwise blocked due to data dependences.
       See comments for function 'do_lrs_reassoc' for detailed 
       descriptions.
    2) Upward code motion: scheduling last uses of LRs can shrink
       and potential reduce the number of overlapping live ranges.
       See comments for function 'get_reg_pressure_change_if_swapped'
       for details. 
    3) Expression tree scheduling: this is a downward code motion pass.
       The objective of this transformation is to make sure the subtrees
       of an expression tree are evaluated sequentially --- i.e., the
       evaluation of one subtree won't start until the previous subtree
       is complete. The evaluation order of the subtrees are determined 
       by the number of temporary registers needed. 
    4) Multi-use expression downward code motion: the objective is move
       the definition downward as close as possible to its uses  when 
       the downward motion does not cause the live range of the RHS LRs 
       to be lengthened. 

    The LRS optimization is composed of the following steps:

    1) Perform loop recognition;

    2) Process all phi statements in the function to map ssa names (
       gimple regs) to reg allocs (i.e., pseudo registers)

    3) walk through the function, and identify LRS regions (innermost
       loops or large BBs in  acyclic regions). For each region larger
       than a threshold.

         3.1) perform live use reference data flow analysis;
         3.2) compute register pressure for the region. If the pressure
              is high;
         3.3) perform a round of expression reassociation to enable more
              LRS opportunities;
         3.4) perform upward code motion to shrink live ranges;
         3.5) perform virtual variable reaching definition data flow analysis;
         3.6) perform downward code motion including subtree scheduling to
              shrink live ranges.
         3.7) perform downward code motion of expression tree with multiple uses.
*/


/* Canonicalized statement used in live range shrinking.  */

typedef struct lrs_stmt
{
  gimple  stmt;
  tree    def;
  tree  **uses;
  size_t  num_uses;
} *lrs_stmt_p;

/* The expression tree representation used in
   live range shinking (downward motion phase). The
   tree is formed by following single use/single def
   chain.  */

typedef struct lrs_tree
{
  /* The gimple statement that defines the root node
     of the expression tree.  */
  gimple root;
  /* The vector of gimple statements that define the inner
     nodes of the expression tree. The statements are in
     the scheduled order in the IL.  */
  VEC(gimple, heap) *tree_nodes;
  /* The vector of values that assoicated with leaf nodes
     of the expression tree.  */
  VEC(tree, heap) *leaf_nodes;
  /* The number of leaf nodes (ssa names) that are not live
     across the root gimple statement.  */
  int num_leaves_not_live_across;
  /* The number of leaves that are live across the root.  */
  int num_leaves_live_across;
  /* The max number of temporary LRs that are needed to evaluate
     this expression tree.  */
  int num_temp_lrs;
} *lrs_tree_p;


typedef tree *treep;
DEF_VEC_P(treep);
DEF_VEC_ALLOC_P(treep, heap);

/* Tree representation for expression trees that are candidates
   for reassociation enabling opportunities for live range shrinking.  */

typedef struct lrs_reassoc_tree
{
  gimple root;
  VEC(gimple, heap) *inner_nodes;
  VEC(tree, heap) *leaf_operands;
  VEC(treep, heap) *use_ref_slots;
  enum tree_code opc;
} *lrs_reassoc_tree_p;

DEF_VEC_P(lrs_reassoc_tree_p);
DEF_VEC_ALLOC_P(lrs_reassoc_tree_p, heap);

/* Enum for register classes.  The partition is an approximation
   at high level and is target independent.  */

enum lrs_reg_class
{
  /* general register class.  */
  lrc_gr,
  /* floating pointer register class.  */
  lrc_fr,
  lrc_num
};

/* The equivalent class of ssa names that need to be allocated 
   to the same register.  */

typedef struct reg_alloc
{
  /* Members (ssa names) of the reg_alloc.  */
  VEC(tree, heap) *members;
  /* reg alloc parent to which this reg alloc is joined.  */
  struct reg_alloc *parent;
} *reg_alloc_p;

DEF_VEC_P(reg_alloc_p);
DEF_VEC_ALLOC_P(reg_alloc_p, heap);

/* This data structure is used to represent the code region
   that is selected for live range shrinking transformation. 
   In this implementation, only two types of regions are 
   supported: 1) inner most natural loop; 2) single basic block
   with size larger than a threshold.  */

typedef struct lrs_region
{
  /* The single entry to the region.  */
  basic_block entry;
  /* The array of exit bbs in the region. An exit bb is a bb 
     in the region with an out edge leaving the region.  */
  basic_block *exits;
  /* The region body as an array of basic block pointers. The
     index of the BB in the array is the id of the BB in the 
     region.  */
  basic_block *body;
  size_t num_bbs;
  size_t num_exits;
  size_t num_stmts;
  /* The width of the bitvector for the use-ref data flow problem.  */
  size_t bitvec_width;
  /* The size (in the number of gimple statements) of the largest
     bb in the region.  */
  unsigned max_bb_size;

  /* The mapping from bb address to region index.  */
  struct pointer_map_t *bb_to_idx_map;

  /* Bitvector (live use-ref problem) arrays. Each 
     array is indexed by the region id of a BB.  */
  sbitmap *bb_use_ref_out_sets;
  sbitmap *bb_use_ref_in_sets;
  sbitmap *bb_use_ref_kill_sets;
  sbitmap *bb_use_ref_gen_sets;

  /* The array of bitvectors representing use-refs that are live
     across gimple statements. The array is indexed by gimple 
     statement id in the region. The gimple statement id is stored
     in the uid field of the gimple statement.  */
  sbitmap *across_stmt_use_ref_sets;
  /* The array of normalized statements. The array is indexed by
     the gimple statement id in the region.  */
  lrs_stmt_p normalized_stmts;

  /* The vector of ssa names that referenced in the region.  */
  VEC(tree, heap) *refed_names;
  /* The set of ssa names that are live (referenced) out of region.  */
  sbitmap region_live_out_names;

  /* The map from SSA names to position range in bitvectors.  */
  struct pointer_map_t *bit_range_map;
  /* The map from SSA names to the bitmask associated with name uses.  */
  struct pointer_map_t *def_bitmask_map;
  /* The map from use references to bit positions in bitvectors  .*/
  struct pointer_map_t *bit_pos_map;

  /* The vector of virtual variables that are referenced in the region.  */
  VEC(tree, heap) *refed_vvars;
  /* The vector of ssa names of the virtual variables.  */
  VEC(tree, heap) *refed_vvar_names;
  /* The map from virtual variable names to the bitvector (
     reaching def problem) bit positions.  */
  struct pointer_map_t *vname_bit_pos_map;
  /* The map from virtual variables to the bitvector (
     reaching def problem) bit position ranges.  */
  struct pointer_map_t *vvar_bit_range_map;

  /* Bitvector (reaching def problem) arrays. Each 
     array is indexed by the region id of a BB.  */
  sbitmap *bb_rd_in_sets;
  sbitmap *bb_rd_out_sets;
  sbitmap *bb_rd_kill_sets;
  sbitmap *bb_rd_gen_sets;

  /* Reach def bitvector array for gimple statements
     in the region.  */
  sbitmap *stmt_rd_sets;
  /* Map from a gimple statement to a lrs_tree that is
     rooted at the statement.  */
  struct pointer_map_t *gimple_to_lrs_tree_map;
  /* Memory pool for lrs_tree objects.  */
  alloc_pool lrs_tree_pool;

  /* Vector of created lrs_reassoc_tree  */
  VEC(lrs_reassoc_tree_p, heap) *lrs_reassoc_trees;
  /* Memory pool for lrs_reassoc_tree objects.  */
  alloc_pool lrs_reassoc_tree_pool;

  /* The number of available registers for each register
     class.  */
  unsigned available_regs[lrc_num];
  /* Computed register pressure for this region.  */
  unsigned reg_pressure[lrc_num];
  /* Computed register pressure for each BB in the region.  */
  unsigned *bb_reg_pressures[lrc_num];

} *lrs_region_p;


#define REG_CLASS_MAP(rc) ira_class_translate[(rc)]

/* Statement order hashmap. The order information
   is used in rank compuation and code motion.  */
static struct pointer_map_t *stmt_order = NULL;
/* The map from ssa namees to the indices of the
   reg allocs.  */
static struct pointer_map_t *reg_alloc_map = NULL;
/* The array of reg allocs.  */
static VEC(tree, heap) **reg_allocs = NULL;
static size_t num_reg_allocs = 0;
/* The map from ssa names to the associated reg allocs.  */
static struct pointer_map_t *tmp_reg_alloc_map = NULL;
static VEC(reg_alloc_p, heap) *reg_alloc_vec = NULL;
static alloc_pool tmp_reg_alloc_pool = NULL;
static unsigned reg_pressure_control_min_bb_size = 0;

struct pending_negates
{
  VEC(tree, heap) *opnds_to_negate;
  VEC(gimple, heap) *stmts_to_fixup;
};
static struct pending_negates pending_negates = {NULL, NULL};

static size_t get_stmt_order (const_gimple);
static void destroy_region (lrs_region_p region);
static void dump_reg_allocs (FILE *file);
static void print_lrs_tree (FILE *file, lrs_tree_p);
static void print_lrs_reassoc_tree (FILE *file, lrs_reassoc_tree_p);

/* A helper function to determine if a code motion phase is needed
   for BB after expression reassociation to reduce register pressure.
   1. It returns false if --param ctrl-repre=0;
   2. It returns true if --param ctrl-regpre=2;
   3. If the parameter value is 1 (the default), it is at the
   compiler's discretion. Currently, it returns true only when largest 
   BB (in REGION)'s size is larger than a given threshold.  */

static int
need_control_reg_pressure (lrs_region_p region)
{
  int control_reg_pressure;

  control_reg_pressure = PARAM_VALUE (PARAM_CONTROL_REG_PRESSURE);
  if (control_reg_pressure == 2)
    return 2;
  if (control_reg_pressure == 1
      && (region->max_bb_size
          > reg_pressure_control_min_bb_size))
    return 1;
  else
    return 0;
}

/* The function checks command line control parameters and returns
   true if upward code motion transformation is enabled. It returns
   false otherwise.  */

static inline bool
do_upward_motion (void)
{
  int code_motion_mode;
  code_motion_mode 
      = PARAM_VALUE (PARAM_REG_PRESSURE_CONTROL_MODE);
  return !!(code_motion_mode & 1);
}

/* The function checks command line control parameters and returns
   true if downward code motion transformation is enabled. It returns
   false otherwise.  */

static inline bool
do_downward_motion (void)
{
  int code_motion_mode;
  code_motion_mode 
      = PARAM_VALUE (PARAM_REG_PRESSURE_CONTROL_MODE);
  return !!(code_motion_mode & 0x2);
}

/* The function checks command line control parameters and returns
   true if reassociation transformation is enabled. It returns
   false otherwise.  */

static inline bool
do_reassoc (void)
{
  int code_motion_mode;
  code_motion_mode 
      = PARAM_VALUE (PARAM_REG_PRESSURE_CONTROL_MODE);
  return !!(code_motion_mode & 0x4);
}

/* The function returns the size of the basic block BB in terms
   of the number of gimple statements in it.  */

static size_t
get_bb_size (basic_block bb)
{
  gimple_stmt_iterator gsi_last;

  gsi_last = gsi_last_bb (bb);
  if (gsi_end_p (gsi_last))
    return 0;

  return get_stmt_order (gsi_stmt (gsi_last));
}

/* The function returns the unique id of the gimple STMT.  */

static inline int
get_stmt_idx_in_region (gimple stmt)
{
  return gimple_uid (stmt);
}

/* The function returns true of BB is included in REGION. If it
   returns true, *IDX is set to the region id of BB in REGION.  */

static bool
get_bb_index_in_region (basic_block bb, lrs_region_p region, int *idx)
{
  void **slot;

  /* pointer map will always return a slot for NULL key.  */
  if (bb == NULL)
    return false;
  slot = pointer_map_contains (region->bb_to_idx_map, bb);
  if (!slot)
    return false;

  *idx = (int) (size_t) *slot;
  return true;
}

/* The function returns the normalized lrs stmt for STMT in REGION.  */

static inline lrs_stmt_p
get_normalized_gimple_stmt (gimple stmt, lrs_region_p region)
{
  int id = get_stmt_idx_in_region (stmt);
  return &region->normalized_stmts[id];
}

/* The tree walk callback function for collecting use refs. *OP
   is the tree node being processed, and *DATA is the pointer to
   the vector of collected uses.  */

static tree
collect_use (tree *op,
             int *unused ATTRIBUTE_UNUSED,
             void *data)
{
  VEC(treep, heap) **stmt_uses = (VEC(treep, heap) **)data;

  if (TREE_CODE (*op) == SSA_NAME && is_gimple_reg (*op))
      VEC_safe_push (treep, heap, *stmt_uses, op);

  return 0;
}

/* The function normalizes STMT into NORM_STMT.  */

static void
normalize_gimple_stmt (gimple stmt, lrs_stmt_p norm_stmt)
{
  size_t i, n;
  VEC(treep, heap) *stmt_uses = NULL;
  tree lhs;

  norm_stmt->stmt = stmt;
  norm_stmt->uses = NULL;
  norm_stmt->def = NULL; 
  norm_stmt->num_uses = 0;

  if (gimple_code (stmt) != GIMPLE_PHI)
    {
      lhs = (gimple_num_ops (stmt)? gimple_op (stmt, 0) : 0);
      if (lhs && is_gimple_reg (lhs) && TREE_CODE (lhs) == SSA_NAME)
        norm_stmt->def = lhs;

      n = gimple_num_ops (stmt);
      for (i = 1; i < n; i++)
        {
          tree *op = gimple_op_ptr (stmt, i);
          if (!op)
            continue;
          walk_tree_without_duplicates (op, collect_use, &stmt_uses);
        }
    }
  else
    {
      lhs = gimple_phi_result (stmt);
      if (is_gimple_reg (lhs))
        {
          norm_stmt->def = lhs;

          n = gimple_phi_num_args (stmt);
          for (i = 0; i < n; i++)
            {
              tree *arg = gimple_phi_arg_def_ptr (stmt, i);
              if (TREE_CODE (*arg) == SSA_NAME && is_gimple_reg (*arg))
                VEC_safe_push (treep, heap, stmt_uses, arg);
            }
        }
    }

  n = norm_stmt->num_uses = VEC_length (treep, stmt_uses);
  if (n)
    {
      norm_stmt->uses = XNEWVEC (treep, n);
      memcpy (norm_stmt->uses, VEC_address (treep, stmt_uses),
              n * sizeof(treep));
    }
  VEC_free (treep, heap, stmt_uses);
}

/* The function normalizes all statements in REGION.  */

static void
normalize_gimple_stmts (lrs_region_p region)
{
  size_t i;

  region->normalized_stmts = XNEWVEC (struct lrs_stmt, region->num_stmts);

  for (i = 0; i < region->num_bbs; i++)
    {
      basic_block bb;
      gimple_stmt_iterator gsi;

      bb = region->body[i];

      for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
        {
          int sidx;
          gimple stmt = gsi_stmt (gsi);
          sidx = get_stmt_idx_in_region(stmt);
          normalize_gimple_stmt (stmt, &region->normalized_stmts[sidx]);
        }
      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
        {
          int sidx;
          gimple stmt = gsi_stmt (gsi);
          sidx = get_stmt_idx_in_region(stmt);
          normalize_gimple_stmt (stmt, &region->normalized_stmts[sidx]);
        }
    }
}

/* The function initializes data members of REGION.  */

static void
init_region (lrs_region_p region)
{
  region->entry = NULL;
  region->exits = NULL;
  region->body = NULL;
  region->num_bbs = 0;
  region->num_exits = 0;
  region->max_bb_size = 0;
  region->num_stmts = 0;
  region->bitvec_width = 0;
  region->bb_to_idx_map = NULL;
  region->bb_use_ref_out_sets = NULL;
  region->bb_use_ref_in_sets = NULL;
  region->bb_use_ref_kill_sets = NULL;
  region->bb_use_ref_gen_sets = NULL;
  region->across_stmt_use_ref_sets = NULL;
  region->normalized_stmts = NULL;
  region->refed_names = NULL;
  region->refed_vvars = NULL;
  region->refed_vvar_names = NULL;
  region->region_live_out_names = NULL;
  region->bit_range_map = NULL;
  region->def_bitmask_map = NULL;
  region->bit_pos_map = NULL;
  region->vname_bit_pos_map = NULL;
  region->vvar_bit_range_map = NULL;
  region->gimple_to_lrs_tree_map = NULL;
  region->lrs_tree_pool = NULL;
  region->lrs_reassoc_tree_pool = NULL;
  region->lrs_reassoc_trees = NULL;
  region->bb_rd_out_sets = NULL;
  region->bb_rd_in_sets = NULL;
  region->bb_rd_kill_sets = NULL;
  region->bb_rd_gen_sets = NULL;
  region->stmt_rd_sets = NULL;
  region->bb_reg_pressures[lrc_gr] = NULL;
  region->bb_reg_pressures[lrc_fr] = NULL;
}

/* The function returns true if BB is the head of a candidate
   region for live range shrinking optimization. Only two types
   of candidates are considered: inner most loop and single BB
   larger than a threshold and that is not in an inner loop. If
   BB is the region head of a loop, *THE_LOOP is set to that loop.  */

static bool
is_region_head (basic_block bb, struct loop **the_loop)
{
  struct loop *loop;

  loop = bb->loop_father;

  if (loop_depth (loop) >= 1 && !loop->inner)
    {
      if (loop->header == bb)
        {
          *the_loop = loop;
          return true;
        }
      else
        return false;
    }
  else
    {
      *the_loop = NULL;
      if (get_bb_size (bb)
          > (size_t) PARAM_VALUE (PARAM_REG_PRESSURE_MIN_BB_FACTOR))
        return true;
      else
        return false;
    }
}

/* The function contructs and returns the pointer to the region
   if BB is a region head.  */

static lrs_region_p
form_region (basic_block bb)
{
  struct loop *loop = NULL;
  struct lrs_region *region;
  size_t i, s = 0;
  int nstmts = 0;

  if (!is_region_head (bb, &loop))
    return NULL;

  region = XNEW (struct lrs_region);
  init_region (region);
  if (loop)
    {
      region->entry = loop->header;
      region->num_bbs = loop->num_nodes;
      region->body = get_loop_body (loop);
    }
  else
    {
      region->entry = bb;
      region->num_bbs = 1;
      region->body = XNEW (basic_block);
      region->body[0] = bb;
    }

  region->bb_to_idx_map = pointer_map_create ();
  s = 5;
  region->exits = XNEWVEC (basic_block, s);
  region->num_exits = 0;
  nstmts = 0;

  for (i = 0; i < region->num_bbs; i++)
    {
      edge e;
      edge_iterator ei;
      basic_block bb;
      gimple_stmt_iterator gsi;
      void **slot;
      size_t sz;

      bb = region->body[i];
      slot = pointer_map_insert (region->bb_to_idx_map, bb);
      *slot = (void*) i;
      sz = get_bb_size (bb);
      if (sz > region->max_bb_size)
        region->max_bb_size = sz;

      for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
        {
          gimple stmt = gsi_stmt (gsi);
          gimple_set_uid (stmt, nstmts++);
        }

      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
        {
          gimple stmt = gsi_stmt (gsi);
          gimple_set_uid (stmt, nstmts++);
        }

      if (loop)
        {
          FOR_EACH_EDGE (e, ei, bb->succs)
            {
              if (!flow_bb_inside_loop_p (loop, e->dest))
                {
                  if (region->num_exits >= s)
                    {
                      s += s;
                      region->exits
                          = XRESIZEVEC (basic_block, region->exits, s);
                    }
                  region->exits[region->num_exits] = bb;
                  region->num_exits++;
                }
            }
        }
      else
        {
          region->exits = XNEW (basic_block);
          region->exits[0] = bb;
          region->num_exits = 1;
        }
    }

  if (!need_control_reg_pressure (region)
      || nstmts >= PARAM_VALUE (PARAM_REG_PRESSURE_MAX_REGION))
    {
      if (dump_file)
        fprintf (dump_file,
                 "Region (Entry BB# %d) is skipped: "
                 "region max bb size = %u, min_size = %u! "
                 "Reason : %s .\n",
                 region->entry->index, region->max_bb_size,
                 reg_pressure_control_min_bb_size,
                 (nstmts >= PARAM_VALUE (PARAM_REG_PRESSURE_MAX_REGION)
                 ? "max region size reached" : "not beneficial"));
      destroy_region (region);
      return NULL;
    }

  region->num_stmts = nstmts;
  normalize_gimple_stmts (region);

  return region;
}

/* The function is used as the callback method in pointer map
   traversal. It destroys the bitmasks in the bitmask map.  */

static bool
destroy_def_bitmask (const void *key ATTRIBUTE_UNUSED, 
                     void **value,
                     void *data ATTRIBUTE_UNUSED)
{
  sbitmap mask;

  gcc_assert (*value);
  mask = (sbitmap)*value;
  sbitmap_free (mask);
  return true;
}

/* The function is used to destroy the definition bitmask map in REGION.  */

static inline void
destroy_def_bitmask_map (lrs_region_p region)
{
  pointer_map_traverse (region->def_bitmask_map, 
                        destroy_def_bitmask,  NULL);
  pointer_map_destroy (region->def_bitmask_map);
}

/* The function detroys normalized statements in REGION.  */

static void
destroy_normalized_stmts (lrs_region_p region)
{
  size_t i;

  for (i = 0; i < region->num_stmts; i++)
  {
    lrs_stmt_p nstmt = &region->normalized_stmts[i];
    if (nstmt->uses)
      free (nstmt->uses);
  }

  free (region->normalized_stmts);
}

/* The function is the callback function in the pointer map traversal
   to destroy the lrs trees.  */

static bool
destroy_lrs_tree (const void *key ATTRIBUTE_UNUSED, void **value,
                  void *data ATTRIBUTE_UNUSED)
{
  lrs_tree_p lrs_tree;

  lrs_tree = (lrs_tree_p)*value;
  VEC_free (gimple, heap, lrs_tree->tree_nodes);
  VEC_free (tree, heap, lrs_tree->leaf_nodes);
  return true;
}

/* The function is used to destroy the lrs tree map and the lrs tree
   memory pool in REGION.  */

static void
destroy_lrs_tree_pool (lrs_region_p region)
{
  if (region->gimple_to_lrs_tree_map)
    {
      pointer_map_traverse (region->gimple_to_lrs_tree_map,
                            destroy_lrs_tree, NULL);
      pointer_map_destroy (region->gimple_to_lrs_tree_map);
    }
  if (region->lrs_tree_pool)
    free_alloc_pool (region->lrs_tree_pool);
}

/* The function is used to destroy a lrs_reassoc_tree REASSOC_TREE.  */

static void
destroy_lrs_reassoc_tree (lrs_reassoc_tree_p reassoc_tree)
{
  VEC_free (gimple, heap, reassoc_tree->inner_nodes);
  VEC_free (tree, heap, reassoc_tree->leaf_operands);
  VEC_free (treep, heap, reassoc_tree->use_ref_slots);
}

/* The function destroys the memory pool for lrs reassociation trees.  */

static void
destroy_lrs_reassoc_tree_pool (lrs_region_p region)
{
  if (region->lrs_reassoc_trees)
    {
      int i = 0;
      int n = VEC_length (lrs_reassoc_tree_p, region->lrs_reassoc_trees);
      for (i = 0; i < n; i++)
	destroy_lrs_reassoc_tree (VEC_index (lrs_reassoc_tree_p,
					     region->lrs_reassoc_trees, i));
      gcc_assert (region->lrs_reassoc_tree_pool);
      free_alloc_pool (region->lrs_reassoc_tree_pool);
    }
}

/* The function reclaims memory used for live range shrinking for REGION.  */

static void
destroy_region (lrs_region_p region)
{
  size_t i;
  if (region->exits)
    free (region->exits);
  if (region->body)
    free (region->body);
  if (region->def_bitmask_map)
    destroy_def_bitmask_map (region);
  if (region->bit_range_map)
    pointer_map_destroy (region->bit_range_map);
  if (region->bit_pos_map)
    pointer_map_destroy (region->bit_pos_map);
  if (region->vname_bit_pos_map)
    pointer_map_destroy (region->vname_bit_pos_map);
  if (region->vvar_bit_range_map)
    pointer_map_destroy (region->vvar_bit_range_map);
  if (region->bb_to_idx_map)
    pointer_map_destroy (region->bb_to_idx_map);
  if (region->bb_use_ref_out_sets)
    sbitmap_vector_free (region->bb_use_ref_out_sets);
  if (region->bb_use_ref_in_sets)
    sbitmap_vector_free (region->bb_use_ref_in_sets);
  if (region->bb_use_ref_gen_sets)
    sbitmap_vector_free (region->bb_use_ref_gen_sets);
  if (region->bb_use_ref_kill_sets)
    sbitmap_vector_free (region->bb_use_ref_kill_sets);
  if (region->across_stmt_use_ref_sets)
    sbitmap_vector_free (region->across_stmt_use_ref_sets);
  if (region->region_live_out_names)
    sbitmap_free (region->region_live_out_names);
  if (region->refed_names)
    VEC_free (tree, heap, region->refed_names);
  if (region->refed_vvars)
    VEC_free (tree, heap, region->refed_vvars);
  if (region->refed_vvar_names)
    VEC_free (tree, heap, region->refed_vvar_names);
  if (region->bb_rd_out_sets)
    sbitmap_vector_free (region->bb_rd_out_sets);
  if (region->bb_rd_in_sets)
    sbitmap_vector_free (region->bb_rd_in_sets);
  if (region->bb_rd_gen_sets)
    sbitmap_vector_free (region->bb_rd_gen_sets);
  if (region->bb_rd_kill_sets)
    sbitmap_vector_free (region->bb_rd_kill_sets);
  if (region->stmt_rd_sets)
    sbitmap_vector_free (region->stmt_rd_sets);
  if (region->bb_reg_pressures[0])
    {
      for (i = 0; i < lrc_num; i++)
        free (region->bb_reg_pressures[i]);
    }
  destroy_normalized_stmts (region);

  destroy_lrs_tree_pool (region);
  destroy_lrs_reassoc_tree_pool (region);

  VEC_free (tree, heap, pending_negates.opnds_to_negate);
  VEC_free (gimple, heap, pending_negates.stmts_to_fixup);
  pending_negates.opnds_to_negate = NULL;
  pending_negates.stmts_to_fixup = NULL;

  free (region);
}

/* The function returns the root node for a union of
   reg_alloc nodes for which RA is a member.  */

static reg_alloc_p
get_reg_alloc_root (reg_alloc_p ra)
{
  reg_alloc_p ra1 = ra, ra2;

  while (ra->parent)
    ra = ra->parent;

  while (ra1->parent)
    {
      ra2 = ra1->parent;
      ra1->parent = ra;
      ra1 = ra2;
    }
  return ra;
}

/* The function joins two reg_alloc nodes RA1 and RA2, and
   returns the root node of the union.  */

static reg_alloc_p
reg_alloc_union (reg_alloc_p ra1, reg_alloc_p ra2)
{
  ra1 = get_reg_alloc_root (ra1);
  ra2 = get_reg_alloc_root (ra2);

  if (ra1 == ra2)
    return ra1;

  ra2->parent = ra1;

  return ra1;
}

/* The function joins a SSA name NM into one register allocation RA.  */

static inline void
join_reg_alloc (reg_alloc_p ra, tree nm)
{
  void **slot;
  VEC_safe_push (tree, heap, ra->members, nm);

  slot = pointer_map_insert (tmp_reg_alloc_map, nm);
  gcc_assert (!*slot);
  *slot = ra;
}

/* The function returns the representative reg_alloc node for ssa name NM.  */

static reg_alloc_p
find_reg_alloc (tree nm)
{
  void **slot;
  reg_alloc_p ra;

  slot = pointer_map_contains (tmp_reg_alloc_map, nm);
  if (!slot)
    return NULL;

  gcc_assert (*slot);
  ra = (reg_alloc_p) *slot;
  return get_reg_alloc_root (ra);
}

/* The function checks if ssa name NM has a register allocation allocated. 
   If not, it will be created and inserted into the map. The reg_alloc node
   found/created is then returned.  */

static reg_alloc_p
find_or_create_reg_alloc (tree nm)
{
  void **slot;
  reg_alloc_p ra;

  slot = pointer_map_insert (tmp_reg_alloc_map, nm);

  if (*slot)
    return get_reg_alloc_root ((reg_alloc_p)*slot);

  ra = (reg_alloc_p) pool_alloc (tmp_reg_alloc_pool);
  ra->members = NULL;
  ra->parent = NULL;
  VEC_safe_push (tree, heap, ra->members, nm);
  *slot = ra;
  VEC_safe_push (reg_alloc_p, heap, reg_alloc_vec, ra);
  return ra;
}

/* The function processes a PHI node and joins the reg_alloc
   of the phi arguments.  */

static void
compute_reg_alloc (gimple phi)
{
  size_t n, i;

  tree res = gimple_phi_result (phi);
  reg_alloc_p ra = find_or_create_reg_alloc (res);

  n = gimple_phi_num_args (phi);
  for (i = 0; i < n; i++)
    {
      reg_alloc_p arg_ra = 0;
      tree arg = gimple_phi_arg_def (phi, i);

      if (TREE_CODE (arg) != SSA_NAME)
        continue;

      arg_ra = find_reg_alloc (arg);
      if (arg_ra)
        ra = reg_alloc_union (ra, arg_ra);
      else
        join_reg_alloc (ra, arg);
    }
}

/* The function is used to process all phi statements
   in basic block BB for reg_alloc creation.  */

static void
compute_reg_allocs (basic_block bb)
{
  gimple_stmt_iterator gsi;

  for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      tree res;
      gimple phi = gsi_stmt (gsi);

      res = gimple_phi_result (phi);
      if (!is_gimple_reg (res))
        continue;

      compute_reg_alloc (phi);
    }
}

/* The function is used to move members (ssa names) of
   a reg_alloc node to the root node of the union. The
   member array of the transferred node is then destroyed.
   Returns the number of reg_alloc roots.  */

static int
finalize_ra_mem (void)
{
  reg_alloc_p ra = 0;
  size_t r, c = 0;

  for (r = 0;
       VEC_iterate (reg_alloc_p, reg_alloc_vec, r, ra);
       r++)
    {
      size_t i;
      tree nm;
      reg_alloc_p real_ra = 0;

      real_ra = get_reg_alloc_root (ra);
      if (real_ra == ra)
        {
          c++;
          continue;
        }

      if (!ra->members)
        continue;

      for (i = 0;
           VEC_iterate (tree, ra->members, i, nm);
           i++)
        VEC_safe_push (tree, heap, real_ra->members, nm);

      VEC_free (tree, heap, ra->members);
      ra->members = 0;
    }

  return c;
}

/* The function maps ssa names to their associated reg_alloc number.  */

static void
finalize_ra_map (void)
{
  reg_alloc_p ra = 0;
  size_t r;

  for (r = 0;
       VEC_iterate (reg_alloc_p, reg_alloc_vec, r, ra);
       r++)
    {
      size_t i;
      reg_alloc_p real_ra = 0;
      tree nm;

      real_ra = get_reg_alloc_root (ra);
      if (ra != real_ra)
        continue;

      if (!real_ra->members)
        continue;

      for (i = 0;
           VEC_iterate (tree, real_ra->members, i, nm);
           i++)
        {
          void **slot = pointer_map_insert (reg_alloc_map, nm);
          *slot = (void *)(size_t) num_reg_allocs;
        }

      reg_allocs[num_reg_allocs++] = real_ra->members;
      real_ra->members = 0;
    }
}

/* The function returns the reg_alloc number/id for ssa
   name NM. It returns -1 if the NM does not map to any
   reg_alloc.  */

static int
get_reg_alloc_id (const tree nm)
{
  void **slot;
  slot = pointer_map_contains (reg_alloc_map, nm);
  if (!slot)
    return -1;
  return (int) (long) *slot;
}

/* The function destroys the temporary reg_alloc map
   used in reg_alloc computation.  */

static void
destroy_tmp_reg_alloc_map (void)
{
  pointer_map_destroy (tmp_reg_alloc_map);
  free_alloc_pool (tmp_reg_alloc_pool);
  tmp_reg_alloc_map = 0;
  tmp_reg_alloc_pool = 0;
  VEC_free (reg_alloc_p, heap, reg_alloc_vec);
  reg_alloc_vec = NULL;
}

/* The function converts the temporary reg_alloc map
   into the final ssa name to reg_alloc id map, and 
   destroyes the temporary map.  */

static void
finalize_reg_allocs (void)
{
  int sz = 0;
  sz = finalize_ra_mem ();
  reg_allocs = XNEWVEC (VEC(tree, heap)*, sz);
  num_reg_allocs = 0;
  finalize_ra_map ();
  destroy_tmp_reg_alloc_map ();
}

/* In use-ref data flow problem, each bit position
   in the bit vector corresponds to a unique 
   reference (read) of a ssa name. All references
   of the same ssa name are allocated contiguously
   in the bitvector, so one ssa name has an associated
   bit position range. This function sets the bit range
   information for ssa name NM in a map. FIRST is the first
   bit position, LAST is the last (included) position. REGION
   is the lrs region.  */

static void
set_def_bit_range (int first, int last,
                   tree nm, lrs_region_p region)
{
  void **slot;
  long range;

  gcc_assert ((first & 0xffff) == first && (last & 0xffff) == last);
  slot = pointer_map_insert (region->bit_range_map, nm);
  range = (first << 16) + last;
  *slot = (void *)range;
}

/* The function retrieves the range of bit position for ssa name NM.
   The first bit position is returned in *FIRST, and the last position
   is in *LAST. REGION is the lrs region.  */

static void
get_def_bit_range (size_t *first, size_t *last,
                   tree nm, lrs_region_p region)
{
  void **slot;
  long range;

  slot = pointer_map_contains (region->bit_range_map, nm);
  range = (long) *slot;
  *first = ((range >> 16) & 0xffff);
  *last = (range & 0xffff);
}

/* The function is used to set the bitmask associated with a ssa name NM. 
   A bitmask has 1 bit set in bit range [first, last] which is computed
   from get_def_bit_range. NM is the ssa name. FIRST and LAST are the first
   and last bit position of the bit range. NUM_BITS is the total width of 
   the bit vector. REGION is the lrs region.  */

static void
set_def_bitmask (tree nm, size_t first, size_t last,
                 size_t num_bits, lrs_region_p region)
{
  void **slot;
  sbitmap bitmask;
  size_t i;

  bitmask = sbitmap_alloc (num_bits);
  sbitmap_zero (bitmask);

  for (i = first; i <= last; i++)
    SET_BIT (bitmask, i);

  slot = pointer_map_insert (region->def_bitmask_map, nm);
  *slot = (void*) bitmask;
}

/* The function returns the bitmask for ssa name NM in REGION.  */

static sbitmap
get_def_bitmask (tree nm, lrs_region_p region)
{
  void **slot;

  slot = pointer_map_contains (region->def_bitmask_map, nm);
  gcc_assert (slot && *slot);
  return (sbitmap) *slot;
}

/* The function returns the register class for a ssa name NM.  */

static inline enum lrs_reg_class
get_nm_reg_class (tree nm)
{
  if (FLOAT_TYPE_P (TREE_TYPE (nm)))
    return lrc_fr;
  return lrc_gr;
}

/* The function maps a use ref USE to a bit position POS in REGION.  */

static void
set_use_ref_bit_pos (tree *use, int pos, lrs_region_p region)
{
  void **slot;

  slot = pointer_map_insert (region->bit_pos_map, use);
  *slot = (void *)(long) pos;
}

/* The function returns the bit position for use ref USE in REGION.  */

static int
get_use_ref_bit_pos (tree *use, lrs_region_p region)
{
  void **slot;

  slot = pointer_map_contains (region->bit_pos_map, use);
  gcc_assert (slot);

  return (int)(long) *slot;
}

/* The function returns the live reference set at the program point 
   immediately after gimple statement STMT. REGION is the lrs region.  */

static inline sbitmap
get_across_stmt_use_ref_set (gimple stmt, lrs_region_p region)
{
  int stmt_idx = get_stmt_idx_in_region (stmt);
  return region->across_stmt_use_ref_sets[stmt_idx];
}

/* The function returns the GEN set of use references for the 
   basic block whose id is BB_RIDX in region REGION.  */

static inline sbitmap
get_bb_use_ref_gen_set (int bb_ridx, lrs_region_p region)
{
  return region->bb_use_ref_gen_sets[bb_ridx];
}

/* The function returns the KILL set of use references for the 
   basic block whose id is BB_RIDX in region REGION.  */

static inline sbitmap
get_bb_use_ref_kill_set (int bb_ridx, lrs_region_p region)
{
  return region->bb_use_ref_kill_sets[bb_ridx];
}

/* The function returns the IN set of use references for the 
   basic block whose id is BB_RIDX in region REGION.  */

static inline sbitmap
get_bb_use_ref_in_set (int bb_ridx, lrs_region_p region)
{
  return region->bb_use_ref_in_sets[bb_ridx];
}

/* The function returns the OUT set of use references for the 
   basic block whose id is BB_RIDX in region REGION.  */

static inline sbitmap
get_bb_use_ref_out_set (int bb_ridx, lrs_region_p region)
{
  return region->bb_use_ref_out_sets[bb_ridx];
}

/* The function merges the use ref IN set of
   basic block DEST_BB_RID into the OUT set of bb
   SRC_BB_RID in REGION.  */

static void
merge_from_in_set_ur (int src_bb_rid, int dest_bb_rid, 
                      lrs_region_p region)
{
  sbitmap dest_in_set, src_out_set;

  dest_in_set = get_bb_use_ref_in_set (dest_bb_rid, region);
  src_out_set = get_bb_use_ref_out_set (src_bb_rid, region);

  sbitmap_a_or_b (src_out_set, src_out_set, dest_in_set);
}

/* The function applies the transfer function on bb BB_RID 
   in region REGION for the live use ref data flow problem.  */

static bool
apply_use_ref_trans_func (int bb_rid, lrs_region_p region)
{
  sbitmap in, out, gen, kill;

  in = get_bb_use_ref_in_set (bb_rid, region);
  out = get_bb_use_ref_out_set (bb_rid, region);
  gen = get_bb_use_ref_gen_set (bb_rid, region);
  kill = get_bb_use_ref_kill_set (bb_rid, region);

  return sbitmap_a_or_b_and_c_compl_cg (in, gen, out, kill);
}

/* The function processes statement STMT and updates GEN set GEN_SET
   and KILL set  KILL_SET in REGION.  */

static void
update_use_ref_gen_kill_sets (gimple stmt, 
                              sbitmap gen_set,
                              sbitmap kill_set,
                              lrs_region_p region)
{
  int i, n;
  tree lhs = 0;
  lrs_stmt_p norm_stmt;

  norm_stmt = get_normalized_gimple_stmt (stmt, region);
  lhs = norm_stmt->def;
  if (lhs)
    {
      sbitmap def_bit_mask;

      def_bit_mask = get_def_bitmask (lhs, region);
      if (kill_set)
        sbitmap_a_or_b (kill_set, kill_set, def_bit_mask);
      sbitmap_a_and_not_b (gen_set, gen_set, def_bit_mask);
    }

  n = norm_stmt->num_uses;
  for (i = 0; i < n; i++)
    {
      int bit_pos;
      tree *op = norm_stmt->uses[i];
      bit_pos = get_use_ref_bit_pos (op, region);
      SET_BIT (gen_set, bit_pos);
    }
}

/* The function processes gimple statement STMT in REGION, and 
   updates the use ref set USE_REF_SET to produce the use ref set
   for the program point just before STMT.  */

static inline void
update_use_ref_set_by_stmt (gimple stmt, sbitmap use_ref_set,
                            lrs_region_p region)
{
  update_use_ref_gen_kill_sets (stmt, use_ref_set, NULL, region);
}

/* The function updates the use ref set GEN_SET by the use in phi node
   PHI via edge E. REGION is the lrs REGION.  */

static void
update_use_ref_gen_set_by_phi (gimple phi, edge e,
                               sbitmap gen_set,
                               lrs_region_p region)
{
    tree res;
    tree *arg;

    res = gimple_phi_result (phi);
    if (!is_gimple_reg (res))
      return;

    arg = PHI_ARG_DEF_PTR_FROM_EDGE (phi, e)->use;
    if (TREE_CODE (*arg) == SSA_NAME)
      SET_BIT (gen_set, get_use_ref_bit_pos (arg, region));
}

/* The function updates the gen or use set (GEN_SET) and 
   the kill set KILL_SET from PHI's definition.  REGION is
   the lrs region.  */

static void
update_use_ref_gen_kill_sets_by_phi (gimple phi,
                                     sbitmap gen_set,
                                     sbitmap kill_set,
                                     lrs_region_p region)
{
    tree res;
    sbitmap def_bit_mask;

    res = gimple_phi_result (phi);
    if (!is_gimple_reg (res))
      return;

    def_bit_mask = get_def_bitmask (res, region);
    if (kill_set)
      sbitmap_a_or_b (kill_set, kill_set, def_bit_mask);
    sbitmap_a_and_not_b (gen_set, gen_set, def_bit_mask);
}

/* This is a wrapper function of update_use_ref_gen_kill_sets_by_phi
   that updates the use ref set USE_REF_SET. PHI is tne phi node, and
   REGION is the lrs region.  */

static inline void
update_use_ref_set_by_phi (gimple phi, sbitmap use_ref_set,
                           lrs_region_p region)
{
  update_use_ref_gen_kill_sets_by_phi (phi, use_ref_set, NULL, region);
}

/* The function computes the gen/kill sets of basic block BB with id
   BB_RIDX for the live use ref problem. REGION is the lrs region.  */

static void
compute_use_ref_gen_kill_set (basic_block bb, int bb_ridx, 
                              lrs_region_p region)
{
  gimple_stmt_iterator gsi;
  sbitmap gen_set, kill_set;
  edge_iterator ei;
  edge e;

  gen_set = get_bb_use_ref_gen_set (bb_ridx, region);
  kill_set = get_bb_use_ref_kill_set (bb_ridx, region);

  /* Firstly check phi uses from succesor bbs.  Treating the use in
     a phi operand to be in the source block of the incoming edge is
     more precise (considering the case some of the operands are constant
     propagated.  */

  FOR_EACH_EDGE (e, ei, bb->succs)
    {
      int didx;
      basic_block dest = e->dest;

      if (get_bb_index_in_region (dest, region, &didx))
        {
          for (gsi = gsi_start_phis (dest); !gsi_end_p (gsi); gsi_next (&gsi))
            {
              gimple phi = gsi_stmt (gsi);
              update_use_ref_gen_set_by_phi (phi, e, gen_set, region);
            }
        }
    }

  for (gsi = gsi_last_bb (bb); !gsi_end_p (gsi); gsi_prev (&gsi))
    {
      gimple stmt = gsi_stmt (gsi);
      update_use_ref_gen_kill_sets (stmt, gen_set, kill_set, region);
    }

  /* Now the phis -- the order of traversing does not matter.  */

  for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple phi = gsi_stmt (gsi);
      update_use_ref_gen_kill_sets_by_phi (phi, gen_set, 
                                           kill_set, region);
    }
}

/* The function updates the map from ssa names to set of their use references.
   OP is the use reference, *OP is the ssa name, MP is the map, and REFED_NAMES
   is a vector of referenced ssa names.  */

static void
add_use_ref (tree *op, struct pointer_map_t *mp,
             VEC(tree, heap) **refed_names)
{
  void **slot;
  slot = pointer_map_insert (mp, *op);
  if (!*slot)
    VEC_safe_push (tree, heap, *refed_names, *op);
  VEC_safe_push (treep, heap, *(VEC(treep, heap)**) slot, op);
}

/* The function is used as a callback for pointer_map traverasl. It is
   used to destroy the use ref vectors pointed by the pointer map's
   slots.  */

static bool
destroy_use_ref_vec (const void *key ATTRIBUTE_UNUSED, void **value,
                     void *data ATTRIBUTE_UNUSED)
{
  VEC(treep, heap) *use_refs;

  if (!*value)
    return true;
  use_refs = (VEC(treep, heap) *)*value;
  VEC_free (treep, heap, use_refs);
  return true;
}

/* The function collects the virtual variables (and their ssa names)
   referenced.  VOP is a tree that may be a ssa name. REFED_VVARS is 
   the vector of referenced virtual variables, and REFED_VVAR_NAMES is
   the vector of referenced virtual variable ssa names. VVAR_SET is
   the pointer set of referenced virtual variables, and VVAR_NAME_SET
   is the pointer set of the referenced virtual variable names.  */

static inline void
add_one_vop (tree vop,
             VEC(tree, heap) ** refed_vvars,
             VEC(tree, heap) ** refed_vvar_names,
             struct pointer_set_t *vvar_set,
             struct pointer_set_t *vvar_name_set)
{
  if (TREE_CODE (vop) == SSA_NAME)
    {
      tree vvar;
      if (!pointer_set_insert (vvar_name_set, vop))
        VEC_safe_push (tree, heap, *refed_vvar_names, vop);

      vvar = SSA_NAME_VAR (vop);

      if (!pointer_set_insert (vvar_set, vvar))
        VEC_safe_push (tree, heap, *refed_vvars, vvar);
    }
}

/* The function collects the virtual variables (and their ssa names)
   referenced.  NORM_STMT is the normalized statement. REFED_VVARS is 
   the vector of referenced virtual variables, and REFED_VVAR_NAMES is
   the vector of referenced virtual variable ssa names. VVAR_SET is
   the pointer set of referenced virtual variables, and VVAR_NAME_SET
   is the pointer set of the referenced virtual variable names.  */

static void
get_vop_operands (lrs_stmt_p norm_stmt,
                  VEC(tree, heap) ** refed_vvars,
                  VEC(tree, heap) ** refed_vvar_names,
                  struct pointer_set_t *vvar_set,
                  struct pointer_set_t *vvar_name_set)
{
  gimple stmt;

  stmt = norm_stmt->stmt;
  if (gimple_code (stmt) != GIMPLE_PHI)
    {
      struct voptype_d *vdefs;
      struct voptype_d *vuses;
      int i, n;

      vuses = gimple_vuse_ops (stmt);
      while (vuses)
        {
          n = VUSE_NUM (vuses);
          for (i = 0; i < n; i++)
            {
              tree vop = VUSE_OP (vuses, i);
              add_one_vop (vop, refed_vvars, refed_vvar_names,
                           vvar_set, vvar_name_set);
            }
          vuses = vuses->next;
        }

      vdefs = gimple_vdef_ops (stmt);
      while (vdefs)
        {
          tree vdef;

          vdef = VDEF_RESULT (vdefs);
          add_one_vop (vdef, refed_vvars, refed_vvar_names,
                       vvar_set, vvar_name_set);
          n = VDEF_NUM (vdefs);
          for (i = 0; i < n; i++)
            {
              tree vop = VDEF_OP (vdefs, i);
              add_one_vop (vop, refed_vvars, refed_vvar_names,
                           vvar_set, vvar_name_set);
            }
          vdefs = vdefs->next;
        }
    }
  else
    {
      int i, n;
      tree lhs;

      lhs = gimple_phi_result (stmt);
      if (!is_gimple_reg (lhs))
        {
          add_one_vop (lhs, refed_vvars, refed_vvar_names,
                       vvar_set, vvar_name_set);
        }

      n = gimple_phi_num_args (stmt);
      for (i = 0; i < n; i++)
        {
          tree arg = gimple_phi_arg_def (stmt, i);
          if (TREE_CODE (arg) == SSA_NAME && !is_gimple_reg (arg))
            add_one_vop (arg, refed_vvars, refed_vvar_names,
                         vvar_set, vvar_name_set);
        }
    }
}

static struct pointer_map_t *orig_nm_order = NULL;

/* The comparison function used in quick sorting of SSA names. The
   names are sorted according to the register allocation ids, or if
   not mapped to registers, their ssa name versions.  */

static int
refed_nm_cmp (const void *p1, const void *p2)
{
  int ra1, ra2;
  const tree *n1 = (const tree *)p1;
  const tree *n2 = (const tree *)p2;
  ra1 = get_reg_alloc_id (*n1);
  ra2 = get_reg_alloc_id (*n2);

  if (ra1 == ra2)
    {
      void **slot;
      int o1, o2;

      slot = pointer_map_contains (orig_nm_order, *n1);
      o1 = (int)(long) *slot;
      slot = pointer_map_contains (orig_nm_order, *n2);
      o2 = (int)(long) *slot;
      gcc_assert (o2 != o1);
      return o2 - o1;
    }

  if (ra2 == -1)
    return 1;
  if (ra1 == -1)
    return -1;

  return ra2 - ra1;
}

/* The function initializes the bit vectors used in the live
   use ref data flow problem for REGION.  */

static void
prepare_bitmaps (lrs_region_p region)
{
  size_t i, nr, k, bit_pos;
  VEC(tree, heap) *refed_names = 0;
  struct pointer_map_t *nm_to_use_ref_map = 0;
  sbitmap region_live_out_nms;
  struct pointer_set_t *vvar_set = 0, *vvar_name_set = 0;

  nm_to_use_ref_map = pointer_map_create ();
  vvar_set = pointer_set_create ();
  vvar_name_set = pointer_set_create ();

  for (i = 0; i < region->num_stmts; i++)
    {
      tree lhs;
      size_t j, n;
      lrs_stmt_p norm_stmt;

      norm_stmt = &region->normalized_stmts[i];
      lhs = norm_stmt->def;

      if (lhs)
        {
          void **slot;
          slot = pointer_map_insert (nm_to_use_ref_map, lhs);
          if (!*slot)
            {
              VEC_safe_push (tree, heap, refed_names, lhs);
              *slot = VEC_alloc (treep, heap, 1);
            }
        }

      n = norm_stmt->num_uses;
      for (j = 0; j < n; j++)
        {
          tree *op = norm_stmt->uses[j];
          add_use_ref (op, nm_to_use_ref_map, &refed_names);
        }

      get_vop_operands (norm_stmt, &region->refed_vvars, 
                        &region->refed_vvar_names, 
                        vvar_set, vvar_name_set);
    }

  nr = VEC_length (tree, refed_names);
  region_live_out_nms = sbitmap_alloc (nr);
  sbitmap_zero (region_live_out_nms);

  /* Now remember original name order.  */
  orig_nm_order = pointer_map_create ();
  for (i = 0; i < nr; i++)
    {
      void **slot;

      slot = pointer_map_insert (orig_nm_order,
                                 VEC_index (tree, refed_names, i));
      *slot = (void *)(long)i;
    }

  /* Sort the refed names.  */
  qsort (VEC_address (tree, refed_names), VEC_length (tree, refed_names),
	 sizeof (tree), refed_nm_cmp);

  for (i = 0; i < nr; i++)
    {
      use_operand_p use_p;
      gimple use_stmt;
      imm_use_iterator iter;
      tree nm = VEC_index (tree, refed_names, i);

      FOR_EACH_IMM_USE_FAST (use_p, iter, nm)
        {
          int bb_idx;

          use_stmt = use_p->loc.stmt;
          /* Conservatively consider  NM is live out of the region.  */
          if (!get_bb_index_in_region (gimple_bb (use_stmt),
                                       region, &bb_idx))
            SET_BIT (region_live_out_nms, i);
        }
    }

  region->bit_pos_map = pointer_map_create ();
  region->bit_range_map = pointer_map_create ();
  region->def_bitmask_map = pointer_map_create ();

  bit_pos = 0;
  for (i = 0; i < nr; i += k)
    {
      size_t width, j, m, rpos;
      void **slot;
      int ra_id;
      bool is_live_out = false;
      VEC(treep, heap) *uses = 0;
      tree nm = VEC_index (tree, refed_names, i);

      ra_id = get_reg_alloc_id (nm);

      /* First compute the number of num of names in
         the same class.  */
      k = 1;
      if (ra_id != -1)
        {
          while (i + k < nr)
            {
              tree nm2;
              nm2 = VEC_index (tree, refed_names, i + k);
              if (get_reg_alloc_id (nm2) != ra_id)
                break;
              k++;
            }
        }

      width = 0;
      rpos = 0;
      for (j = i; j < i + k; j++)
        {
          tree nm2;

          nm2 = VEC_index (tree, refed_names, j);
          uses = 0;
          slot = pointer_map_contains (nm_to_use_ref_map, nm2);
          if (*slot)
            uses = (VEC(treep, heap) *)*slot;
          width += VEC_length (treep, uses);

          if (TEST_BIT (region_live_out_nms, j))
            is_live_out = true;

          if (uses)
            for (m = 0; m < VEC_length (treep, uses); m++)
              {
                set_use_ref_bit_pos (VEC_index (treep, uses, m),
                                     bit_pos + rpos, region);
                rpos++;
              }
        }
      gcc_assert (rpos == width);

      if (is_live_out)
        width++;

      /* Reserve one bit for unused defs for simplicity.  */
      if (!width)
        width++;

      for (j = i; j < i + k; j++)
        {
          tree nm2 = VEC_index (tree, refed_names, j);
          set_def_bit_range (bit_pos, bit_pos + width - 1, nm2, region);
        }

      bit_pos += width;
    }

  region->bitvec_width = bit_pos;

  for (i = 0; i < nr; i++)
    {
      size_t first, last;
      tree nm = VEC_index (tree, refed_names, i);

      get_def_bit_range (&first, &last, nm, region);
      set_def_bitmask (nm, first, last,
                       region->bitvec_width, region);
    }

  region->bb_use_ref_out_sets = sbitmap_vector_alloc (region->num_bbs,
                                                      region->bitvec_width);
  sbitmap_vector_zero (region->bb_use_ref_out_sets, region->num_bbs);

  region->bb_use_ref_in_sets = sbitmap_vector_alloc (region->num_bbs,
                                                     region->bitvec_width);
  sbitmap_vector_zero (region->bb_use_ref_in_sets, region->num_bbs);

  region->bb_use_ref_gen_sets = sbitmap_vector_alloc (region->num_bbs,
                                                      region->bitvec_width);
  sbitmap_vector_zero (region->bb_use_ref_gen_sets, region->num_bbs);

  region->bb_use_ref_kill_sets = sbitmap_vector_alloc (region->num_bbs,
                                                       region->bitvec_width);
  sbitmap_vector_zero (region->bb_use_ref_kill_sets, region->num_bbs);

  region->across_stmt_use_ref_sets = sbitmap_vector_alloc (region->num_stmts,
                                                           region->bitvec_width);
  sbitmap_vector_zero (region->across_stmt_use_ref_sets, region->num_stmts);

  /* Now initialize the exit BB's live out use ref sets.  */
  nr = VEC_length (tree, refed_names);
  for (i = 0; i < nr; i++)
    {
      if (TEST_BIT (region_live_out_nms, i))
        {
          size_t j;
          size_t first, last;
          get_def_bit_range (&first, &last,
                             VEC_index (tree, refed_names, i),
                             region);

          for (j = 0; j < region->num_exits; j++)
            {
              int ridx = 0;
              get_bb_index_in_region (region->exits[j], region, &ridx);
              SET_BIT (region->bb_use_ref_out_sets[ridx], last);
            }
        }
    }

  region->region_live_out_names = region_live_out_nms;
  region->refed_names = refed_names;

  pointer_map_traverse(nm_to_use_ref_map, destroy_use_ref_vec, NULL);
  pointer_map_destroy (nm_to_use_ref_map);
  pointer_set_destroy (vvar_set);
  pointer_set_destroy (vvar_name_set);
  pointer_map_destroy (orig_nm_order);
  orig_nm_order = NULL;
}

/* From the solution set of the use ref data flow problem, this function
   computes the live use-ref sets for each program point after each statement
   in region REGION.  */

static void
compute_live_use_ref_set_for_stmts (lrs_region_p region)
{
  size_t i;
  basic_block bb;
  gimple_stmt_iterator gsi;
  sbitmap tmp_set;

  tmp_set = sbitmap_alloc (region->bitvec_width);
  for (i = 0; i < region->num_bbs; i++)
    {
      sbitmap bb_out_set;
      VEC(gimple, heap) *phis = 0;
      int j;
      edge_iterator ei;
      edge e;

      bb = region->body[i];
      bb_out_set = region->bb_use_ref_out_sets[i];
      sbitmap_copy (tmp_set, bb_out_set);

      /* Firstly check phi uses from succesor bbs.  */
      FOR_EACH_EDGE (e, ei, bb->succs)
        {
          int didx;
          basic_block dest = e->dest;

          if (get_bb_index_in_region (dest, region, &didx))
            {
              for (gsi = gsi_start_phis (dest); !gsi_end_p (gsi); gsi_next (&gsi))
                {
                  gimple phi = gsi_stmt (gsi);
                  update_use_ref_gen_set_by_phi (phi, e, tmp_set, region);
                }
            }
        }

      for (gsi = gsi_last_bb (bb); !gsi_end_p (gsi); gsi_prev (&gsi))
        {
          int stmt_idx;
          gimple stmt = gsi_stmt (gsi);

          stmt_idx = get_stmt_idx_in_region (stmt);
          sbitmap_copy (region->across_stmt_use_ref_sets[stmt_idx],
                        tmp_set);
          update_use_ref_set_by_stmt (stmt, tmp_set, region);
        }

      for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
        VEC_safe_push (gimple, heap, phis, gsi_stmt (gsi));

      if (phis)
        for (j = VEC_length (gimple, phis) - 1; j >= 0; j--)
          {
            int stmt_id;
            gimple phi = VEC_index (gimple, phis, j);
            stmt_id = get_stmt_idx_in_region (phi);
            sbitmap_copy (region->across_stmt_use_ref_sets[stmt_id], tmp_set);
            update_use_ref_set_by_phi (phi, tmp_set, region);
          }
    }

  sbitmap_free (tmp_set);
}

/* The function returns true if the region REGION has high register
   pressure (general register class), i.e., max register required
   exceeds the number of registers available.  */

static inline bool
has_high_gr_reg_pressure (lrs_region_p region)
{
  return (region->available_regs[lrc_gr]
          <= region->reg_pressure[lrc_gr]);
}

/* The function returns true if the region REGION has high register
   pressure (float register class), i.e., max register required
   exceeds the number of registers available.  */

static inline bool
has_high_fr_reg_pressure (lrs_region_p region)
{
  return (region->available_regs[lrc_fr]
          <= region->reg_pressure[lrc_fr]
          && region->available_regs[lrc_fr] != 0);
}

/* The function returns true if the region REGION has high register
   pressure.  */

static inline bool
has_high_reg_pressure (lrs_region_p region)
{
  return (has_high_gr_reg_pressure (region)
          || has_high_fr_reg_pressure (region));
}


/* The function returns true if ssa name LR has any use reference bit
   set in bitvector BITVEC.  */

static inline bool
is_lr_live (tree lr, sbitmap bitvec, lrs_region_p region)
{
  size_t first, last;
  bool is_live;

  get_def_bit_range (&first, &last, lr, region);
  is_live = !sbitmap_range_empty_p (bitvec, first, last - first + 1);

  return is_live;
}

/* The function computes the number of LRs that have any use reference
   bit set in bitvector BITVEC in REGION.  The number of general register
   class LRs is set in *NGR and the number of float register class
   LRs is stored in *NFR.  */

static void
get_num_live_lrs (sbitmap bitvec, lrs_region_p region,
                  unsigned *ngr, unsigned *nfr)
{
  int i, n;
  unsigned gr_pressure = 0;
  unsigned fr_pressure = 0;

  n = VEC_length (tree, region->refed_names);

  for (i = 0; i < n; i++)
    {
      bool is_live;
      tree nm = VEC_index (tree, region->refed_names, i);

      is_live = is_lr_live (nm, bitvec, region);
      if (is_live)
        {
          if (get_nm_reg_class  (nm) == lrc_fr)
            fr_pressure++;
          else
            gr_pressure++;
        }
    }
  *ngr = gr_pressure;
  *nfr = fr_pressure;
}

/* The function computes register pressure for basic block BB (with id BB_RIDX)
   in region REGION.  */

static void
compute_reg_pressure_bb (basic_block bb, int bb_ridx, lrs_region_p region)
{

  gimple_stmt_iterator gsi;
  unsigned bb_gr_pressure = 0;
  unsigned bb_fr_pressure = 0;

  for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      int id;
      unsigned ngr, nfr;
      gimple stmt = gsi_stmt (gsi);

      id = get_stmt_idx_in_region (stmt);
      get_num_live_lrs (region->across_stmt_use_ref_sets[id],
                        region, &ngr, &nfr);
      if (ngr > bb_gr_pressure)
        bb_gr_pressure = ngr;
      if (nfr > bb_fr_pressure)
        bb_fr_pressure = nfr;
    }

  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      int id;
      unsigned ngr, nfr;
      gimple stmt = gsi_stmt (gsi);

      id = get_stmt_idx_in_region (stmt);
      get_num_live_lrs (region->across_stmt_use_ref_sets[id],
                        region, &ngr, &nfr);
      if (ngr > bb_gr_pressure)
        bb_gr_pressure = ngr;
      if (nfr > bb_fr_pressure)
        bb_fr_pressure = nfr;
    }

  region->bb_reg_pressures[lrc_gr][bb_ridx] = bb_gr_pressure;
  region->bb_reg_pressures[lrc_fr][bb_ridx] = bb_fr_pressure;
  
  if (bb_gr_pressure > region->reg_pressure[lrc_gr])
    region->reg_pressure[lrc_gr] = bb_gr_pressure;
  if (bb_fr_pressure > region->reg_pressure[lrc_fr])
    region->reg_pressure[lrc_fr] = bb_fr_pressure;
}


/* The function computes register pressure for region REGION.  */

static void
compute_reg_pressure (lrs_region_p region)
{
  size_t i, j, nr;
  struct pointer_set_t *mode_set;
  VEC(int, heap) *refed_modes[lrc_num];

  nr = VEC_length (tree, region->refed_names);
  mode_set = pointer_set_create ();
  gcc_assert (lrc_num == 2);
  refed_modes[0] = NULL;
  refed_modes[1] = NULL;

  for (i = 0; i < nr; i++)
    {
      enum machine_mode mode;
      enum lrs_reg_class rc;
      tree nm = VEC_index (tree, region->refed_names, i);

      mode = TYPE_MODE (TREE_TYPE (nm));
      rc = get_nm_reg_class (nm);
      if (!pointer_set_insert (mode_set, (void *)(long) mode))
        VEC_safe_push (int, heap,
                       refed_modes[rc], (int) mode);
    }

  for (i = 0; i < lrc_num; i++)
    {
      size_t k;
      region->available_regs[i] = 0;

      for (k = 0; k < FIRST_PSEUDO_REGISTER; k++)
        {
          bool is_reg_ok = false;
          enum reg_class rc = REGNO_REG_CLASS (k);
          for (j = 0; j < VEC_length (int, refed_modes[i]); j++)
            {
              enum machine_mode mode;
              mode = (enum machine_mode) VEC_index (int, refed_modes[i], j);
              if (HARD_REGNO_MODE_OK (k, mode) && !fixed_regs[k]
                  && ((i == lrc_gr && REG_CLASS_MAP (rc) == GENERAL_REGS)
                      || (i == lrc_fr && REG_CLASS_MAP (rc) != GENERAL_REGS)))
                {
                  is_reg_ok = true;
                  break;
                }
            }
          if (is_reg_ok)
            region->available_regs[i]++;
        }
      region->reg_pressure[i] = 0;
      region->bb_reg_pressures[i] = XNEWVEC (unsigned, region->num_bbs);
    }

  for (i = 0; i < region->num_bbs; i++)
    compute_reg_pressure_bb (region->body[i], i, region);

  pointer_set_destroy (mode_set);
  VEC_free (int, heap, refed_modes[0]);
  VEC_free (int, heap, refed_modes[1]);
}

/* The function performs initialization for use ref data flow
   analysis for region REGION.  */

static void
initialize_data_flow_ur (lrs_region_p region)
{
  size_t i;

  prepare_bitmaps (region);

  for (i = 0; i < region->num_bbs; i++)
    compute_use_ref_gen_kill_set (region->body[i], i, region);
}

static void dump_data_flow_result (lrs_region_p, const char *);

/* The function performs live use reference data flow analysis, which
   is a backward data flow problem similar to live variable analysis.  */

static void
perform_data_flow_ur (lrs_region_p region)
{
  sbitmap worklist;
  size_t i;

  initialize_data_flow_ur (region);

  worklist = sbitmap_alloc (region->num_bbs);
  sbitmap_zero (worklist);

  for (i = 0; i < region->num_exits; i++)
    {
      int ridx = 0;
      bool fd;

      fd = get_bb_index_in_region (region->exits[i], region, &ridx);
      gcc_assert (fd);
      SET_BIT (worklist, ridx);
    }

  while (!sbitmap_empty_p (worklist))
    {
      int bb_rid;
      basic_block bb;
      edge e;
      edge_iterator ei;

      bb_rid = sbitmap_first_set_bit (worklist);
      RESET_BIT (worklist, bb_rid);
      bb = region->body[bb_rid];

      FOR_EACH_EDGE (e, ei, bb->succs)
        {
          int didx;

          if (get_bb_index_in_region (e->dest, region, &didx))
            merge_from_in_set_ur (bb_rid, didx, region);
        }

      if (apply_use_ref_trans_func (bb_rid, region))
        {
          FOR_EACH_EDGE (e, ei, bb->preds)
            {
              int pidx;

              if (get_bb_index_in_region (e->src, region, &pidx))
                SET_BIT (worklist, pidx);
            }
        }
    }

  sbitmap_free (worklist);

  compute_live_use_ref_set_for_stmts (region);

  compute_reg_pressure (region);

  dump_data_flow_result (region, "Before code motion");
}

/* This is the comparison function used in sorting of virtual
   ssa names.  The purpose of the sorting is to put all ssa names
   from the same variable together.  */

static int
refed_vnm_cmp (const void *p1, const void *p2)
{
  tree v1, v2;
  const tree n1 = *(const tree *)p1;
  const tree n2 = *(const tree *)p2;

  v1 = SSA_NAME_VAR (n1);
  v2 = SSA_NAME_VAR (n2);

  if (v1 == v2)
    return SSA_NAME_VERSION (n2) - SSA_NAME_VERSION (n1);

  return DECL_UID (v2) - DECL_UID (v1);
}

/* The function maps virtual name VNM to a bit position POS.  */

static void
set_vnm_bit_pos (tree vnm, int pos, lrs_region_p region)
{
  void **slot;

  slot = pointer_map_insert (region->vname_bit_pos_map, vnm);
  *slot = (void *)(long) pos;
}

/* The function returns the bit position of virtual name VNM.  */

static int
get_vnm_bit_pos (tree vnm, lrs_region_p region)
{
  void **slot;

  slot = pointer_map_contains (region->vname_bit_pos_map, vnm);
  gcc_assert (slot);

  return (int)(size_t)*slot;
}

/* The function maps virtual variable VVAR to bit position range
   [first, last].  */

static void
set_vvar_bit_range (int first, int last,
                    tree vvar, lrs_region_p region)
{
  void **slot;
  long range;

  slot = pointer_map_insert (region->vvar_bit_range_map, vvar);
  range = (first << 16) + last;
  *slot = (void *)(long) range;
}

/* The function gets the bit position range for virtual variable
   VVAR.  The first position is stored in *FIRST, and last position
   is in *LAST.  */

static void
get_vvar_bit_range (size_t *first, size_t *last,
                    tree vvar, lrs_region_p region)
{
  void **slot;
  long range;

  slot = pointer_map_contains (region->vvar_bit_range_map, vvar);
  range = (long)(size_t) *slot;
  *first = ((range >> 16) & 0xffff);
  *last = (range & 0xffff);
}

/* The function computes the gen and kill sets for basic block BB
   with id BB_RIDX in region REGION.  The df problem is virtual 
   variable reaching definitions.  */

static void
compute_rd_gen_kill_set (basic_block bb, int bb_ridx, 
                         lrs_region_p region);

/* The function initializes the virtual variable reaching definition
   data flow problem for region REGION.  */

static void
initialize_data_flow_rd (lrs_region_p region)
{
  int i, n, nb, bit_first = 0, bit_last = -1, entry_rid = 0;
  tree vvar; 

  region->vname_bit_pos_map = pointer_map_create ();
  region->vvar_bit_range_map = pointer_map_create ();
  vvar = NULL;
  qsort (VEC_address (tree, region->refed_vvar_names), 
         VEC_length (tree, region->refed_vvar_names),
	 sizeof (tree), refed_vnm_cmp);

  n = VEC_length (tree, region->refed_vvar_names);
  for (i = 0; i < n; i++)
    {
      tree cur_vvar;
      tree vnm = VEC_index (tree, region->refed_vvar_names, i);

      set_vnm_bit_pos (vnm, i, region);
      cur_vvar = SSA_NAME_VAR (vnm);
      if (cur_vvar != vvar)
        {
          if (vvar)
            set_vvar_bit_range (bit_first, bit_last,
                                vvar, region);
          bit_first = bit_last + 1; 
          vvar = cur_vvar;
        }
      bit_last = i;
    }
  if (vvar)
    set_vvar_bit_range (bit_first, bit_last,
                        vvar, region);

  region->bb_rd_out_sets = sbitmap_vector_alloc (region->num_bbs, n);
  sbitmap_vector_zero (region->bb_rd_out_sets, region->num_bbs);
  region->bb_rd_in_sets = sbitmap_vector_alloc (region->num_bbs, n);
  sbitmap_vector_zero (region->bb_rd_in_sets, region->num_bbs);
  region->bb_rd_gen_sets = sbitmap_vector_alloc (region->num_bbs, n); 
  sbitmap_vector_zero (region->bb_rd_gen_sets, region->num_bbs);
  region->bb_rd_kill_sets = sbitmap_vector_alloc (region->num_bbs, n);
  sbitmap_vector_zero (region->bb_rd_kill_sets, region->num_bbs);
  region->stmt_rd_sets = sbitmap_vector_alloc (region->num_stmts, n);
  sbitmap_vector_zero (region->stmt_rd_sets, region->num_stmts);

  nb = region->num_bbs;
  for (i = 0; i < nb; i++)
    compute_rd_gen_kill_set (region->body[i], i, region);

  get_bb_index_in_region (region->entry, region, &entry_rid);
  /* Now initialize the entry's in-set.  */
  for (i = 0; i < n; i++)
    {
      gimple def;
      basic_block bb;
      int rid;
      tree vnm = VEC_index (tree, region->refed_vvar_names, i);

      def = SSA_NAME_DEF_STMT (vnm);
      bb = gimple_bb (def);
      if (!get_bb_index_in_region (bb, region, &rid))
        SET_BIT (region->bb_rd_in_sets[entry_rid], i);
    }
}

/* The function returns the reaching def set before statement
   STMT in region REGION.  */

static inline sbitmap
get_stmt_rd_set (gimple stmt, lrs_region_p region)
{
  int stmt_idx = get_stmt_idx_in_region (stmt);
  return region->stmt_rd_sets[stmt_idx];
}

/* The function returns the reaching def GEN set for basic block
   BB_RIDX in region REGION.  */

static inline sbitmap
get_bb_rd_gen_set (int bb_ridx, lrs_region_p region)
{
  return region->bb_rd_gen_sets[bb_ridx];
}

/* The function returns the reaching def KILL  set for basic block
   BB_RIDX in region REGION.  */

static inline sbitmap
get_bb_rd_kill_set (int bb_ridx, lrs_region_p region)
{
  return region->bb_rd_kill_sets[bb_ridx];
}

/* The function returns the reaching def IN set for basic block
   BB_RIDX in region REGION.  */

static inline sbitmap
get_bb_rd_in_set (int bb_ridx, lrs_region_p region)
{
  return region->bb_rd_in_sets[bb_ridx];
}

/* The function returns the reaching def OUT set for basic block
   BB_RIDX in region REGION.  */

static inline sbitmap
get_bb_rd_out_set (int bb_ridx, lrs_region_p region)
{
  return region->bb_rd_out_sets[bb_ridx];
}

/* The function merges OUT set from source block SRC_BB_RID
   into the IN set of DEST_BB_RID in REGION.  The DF problem
   is the reaching virtual variable definition.  */ 

static void
merge_from_out_set_rd (int dest_bb_rid, int src_bb_rid, 
                       lrs_region_p region)
{
  sbitmap dest_in_set, src_out_set;

  dest_in_set = get_bb_rd_in_set (dest_bb_rid, region);
  src_out_set = get_bb_rd_out_set (src_bb_rid, region);

  sbitmap_a_or_b (dest_in_set, dest_in_set, src_out_set);
}

/* The function applies the transfer function (reaching def)
   for block BB_RID in REGION.  */

static bool
apply_rd_trans_func (int bb_rid, lrs_region_p region)
{
  sbitmap in, out, gen, kill;

  in = get_bb_rd_in_set (bb_rid, region);
  out = get_bb_rd_out_set (bb_rid, region);
  gen = get_bb_rd_gen_set (bb_rid, region);
  kill = get_bb_rd_kill_set (bb_rid, region);

  return sbitmap_a_or_b_and_c_compl_cg (out, gen, in, kill);
}

/* The function updates the GEN set GEN_SET and KILL set KILL_SET by
   processing statement STMT in region REGION.  */

static void
update_rd_gen_kill_sets (gimple stmt, sbitmap gen_set,
                         sbitmap kill_set,
                         lrs_region_p region)
{
  struct voptype_d *vdefs;

  vdefs = gimple_vdef_ops (stmt);
  while (vdefs)
    {
      tree vdef, vvar;
      size_t first, last, i, pos;

      /* The result of the reaching def analysis is used for
         checking violation of data dependency (anti-dependency)
         during downward code motion  -- not for the purpose of redundancy
         elimination or dead code elimination.  What we care about is whether
         there is most recent definition that can block the downward motion.
         For this reason, all may-def or partial defs of a virtual operand
         are considered a strong kill.  For instance:

         <example 1 start>

         *s = ...  (0)  {VDEF: vname_v1 }
         ...
         t = *s;   (1) statement to be moved {VUSE: vname_v1 }

         *p = .... (2)  {VDEF: vname_v2, VUSE: vname_v1 }

         ....
         // Since *p is a may def, both vname_v1 and vname_v2 
         // reach this program point, but we do not need to propagate
         // vname_v1 to this point in order to block the code motion of (1).
         x = t + y (3)  <-- check if (1) can be moved just before (3)

         <example 1 end>


         The reason of this handling is to allow more agressive code motion. 
         For instance, if (2) appears before (0), it is ok to move (1) before (3). 
         This can be archieve by strong kill.

         <example 2 start>

         *p = .... (2)  {VDEF: vname_v2 }

         *s = ...  (0)  {VDEF: vname_v1  VUSE: vname_v2 }
         ...
         t = *s;   (1) statement to be moved {VUSE: vname_v1 }
         ....
         // It is legal to move (1) just before (3).
         x = t + y (3)  <-- check if (1) can be moved just before (3)

         <example 2 end>

      */

      vdef = VDEF_RESULT (vdefs);
      vvar = SSA_NAME_VAR (vdef);
      get_vvar_bit_range (&first, &last, vvar, region);
      pos = get_vnm_bit_pos (vdef,  region);
      for (i = first; i <= last; i++)
        {
          RESET_BIT (gen_set, i);
          if (kill_set)
            SET_BIT (kill_set, i);
        }
      SET_BIT (gen_set, pos);
      if (kill_set)
        RESET_BIT (kill_set, pos);
      vdefs = vdefs->next;
    }
}

/* The function updates the GEN set GEN_SET and KILL set KILL_SET by
   processing phi node STMT in region REGION.  */

static void
update_rd_gen_kill_sets_by_phi (gimple stmt, sbitmap gen_set,
                                sbitmap kill_set,
                                lrs_region_p region)
{
  tree  vvar;
  size_t first, last, i, pos;
  tree lhs = gimple_phi_result (stmt);
  if (!is_gimple_reg (lhs) && TREE_CODE (lhs) == SSA_NAME)
    {
      vvar = SSA_NAME_VAR (lhs);
      get_vvar_bit_range (&first, &last, vvar, region);
      pos = get_vnm_bit_pos (lhs,  region);
      for (i = first; i <= last; i++)
        {
          RESET_BIT (gen_set, i);
          if (kill_set) 
            SET_BIT (kill_set, i);
        }
      SET_BIT (gen_set, pos);
      if (kill_set) 
        RESET_BIT (kill_set, pos);
    }
}

/* The function computes the GEN/KILL sets for basic block BB
   with id BB_RIDX in region REGION.  */

static void
compute_rd_gen_kill_set (basic_block bb, int bb_ridx, 
                         lrs_region_p region)
{
  gimple_stmt_iterator gsi;
  sbitmap gen_set, kill_set;

  gen_set = get_bb_rd_gen_set (bb_ridx, region);
  kill_set = get_bb_rd_kill_set (bb_ridx, region);

  for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple phi = gsi_stmt (gsi);
      update_rd_gen_kill_sets_by_phi (phi, gen_set, 
                                      kill_set, region);
    }

  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple stmt = gsi_stmt (gsi);
      update_rd_gen_kill_sets (stmt, gen_set, kill_set, region);
    }
}

/* The function computes the reaching def sets for  program points
   before all statements in region REGION.  */

static void
compute_rd_set_for_stmts (lrs_region_p region)
{
  size_t i, n;
  basic_block bb;
  gimple_stmt_iterator gsi;
  sbitmap tmp_set;

  n = VEC_length (tree, region->refed_vvar_names);
  tmp_set = sbitmap_alloc (n);

  for (i = 0; i < region->num_bbs; i++)
    {
      sbitmap bb_in_set;

      bb = region->body[i];
      bb_in_set = region->bb_rd_in_sets[i];
      sbitmap_copy (tmp_set, bb_in_set);

      for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
        {
          int stmt_id;
          gimple phi = gsi_stmt (gsi);
          stmt_id = get_stmt_idx_in_region (phi);
          sbitmap_copy (region->stmt_rd_sets[stmt_id], tmp_set);
          update_rd_gen_kill_sets_by_phi (phi, tmp_set, NULL,  region);
        }


      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
        {
          int stmt_idx;
          gimple stmt = gsi_stmt (gsi);

          stmt_idx = get_stmt_idx_in_region (stmt);
          sbitmap_copy (region->stmt_rd_sets[stmt_idx], tmp_set);
          update_rd_gen_kill_sets (stmt, tmp_set, NULL, region);
        }
    }
  sbitmap_free (tmp_set);
}

static void dump_data_flow_result_rd (lrs_region_p);

/* The function performs virtual variable reaching def data flow
   analysis for region REGION.  */

static void
perform_data_flow_rd (lrs_region_p region)
{
  int ridx;
  sbitmap worklist;
  bool fd;

  if (VEC_length (tree, region->refed_vvars) == 0)
    return;

  initialize_data_flow_rd (region);

  worklist = sbitmap_alloc (region->num_bbs);
  sbitmap_zero (worklist);

  fd = get_bb_index_in_region (region->entry, region, &ridx);
  gcc_assert (fd);
  SET_BIT (worklist, ridx);

  while (!sbitmap_empty_p (worklist))
    {
      int bb_rid;
      basic_block bb;
      edge e;
      edge_iterator ei;

      bb_rid = sbitmap_first_set_bit (worklist);
      RESET_BIT (worklist, bb_rid);
      bb = region->body[bb_rid];

      FOR_EACH_EDGE (e, ei, bb->preds)
        {
          int sidx;

          if (get_bb_index_in_region (e->src, region, &sidx))
            merge_from_out_set_rd (bb_rid, sidx, region);
        }

      if (apply_rd_trans_func (bb_rid, region))
        {
          FOR_EACH_EDGE (e, ei, bb->succs)
            {
              int pidx;

              if (get_bb_index_in_region (e->dest, region, &pidx))
                SET_BIT (worklist, pidx);
            }
        }
    }

  compute_rd_set_for_stmts (region);
  dump_data_flow_result_rd (region);

  sbitmap_free (worklist);
}

/* The function computes the order of statements in
   BB.  Phi nodes are not traversed, and they all
   have the default order of 0.  */

static void
compute_stmt_order (basic_block bb)
{
  gimple_stmt_iterator gsi;
  /* Order starts from one.  Zero is reserved for phis.  */
  size_t order = 1;

  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      void **slot;
      gimple stmt = gsi_stmt (gsi);
      slot = pointer_map_insert (stmt_order, stmt);
      gcc_assert (!*slot);
      *slot = (void *) order;
      order++;
      gimple_set_visited (stmt, false);
    }
}

/* Returns the order of STMT in its current basic block.
   Returns 0 for phi nodes, and -1 if STMT is created
   after the stmt order map is created (to indicate
   that no order information is available).  */

static size_t
get_stmt_order (const_gimple stmt)
{
  void **slot;

  if (gimple_code (stmt) == GIMPLE_PHI)
    return 0;

  slot = pointer_map_contains (stmt_order, stmt);
  return slot ? (size_t) *slot : (size_t)-1U;
}

/* The function resets the order of STMT to NEW_ORDER after
   code motion.  NEW_ORDER for STMT is the order of the stmt
   it is inserted after/before.  */

static void
reset_stmt_order (const_gimple stmt, size_t new_order)
{
  void **slot = pointer_map_contains (stmt_order, stmt);
  if (!slot)
    /* New stmt can be created in factorization/undistribution.  */
    slot = pointer_map_insert (stmt_order, stmt);
  *slot = (void *) new_order;
}

/* This function checks if STMT1, which appears in the same
   basic block as STMT2, actually precedes STMT2 in the IL
   stream.  */

static bool
is_preceding_in_real_order (gimple stmt1, gimple stmt2)
{
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt1);
  bool found = false;

  gcc_assert (gimple_code (stmt1) != GIMPLE_PHI);
  for (; !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple stmt = gsi_stmt (gsi);
      if (stmt == stmt2)
        {
          found = true;
          break;
        }
    }

  return found;
}

/* Returns true if STMT1 dominates STMT2.  This query function
   is always invoked with STMT1 being the dependence predecessor
   and STMT2 being the successor.  When they are in the same basic
   block, their statement orders are used for determining dominance.
   Note that after code motion, statements that are moved get the
   new order from the statement of their insertion point.  As a result,
   two statements may have the same order in the same BB.  When
   dominance relationship is checked on such two statements, their
   real statement order needs to be examined which means traversing
   the statement list.  */

static bool
is_dominating (gimple stmt1, gimple stmt2)
{
  basic_block bb1 = gimple_bb (stmt1);
  basic_block bb2 = gimple_bb (stmt2);

  if (bb1 == bb2)
    {
      size_t stmt_order1 = get_stmt_order (stmt1);
      size_t stmt_order2 = get_stmt_order (stmt2);

      gcc_assert (stmt_order1 != (size_t)-1U
                  && stmt_order2 != (size_t)-1U);

      if (stmt_order1 == 0)
        {
          gcc_assert (gimple_code (stmt1) == GIMPLE_PHI);
          /* It does not matter if the other stmt is a phi
             or not -- as the code motion insertion point
             is guaranteed to be dominated by the phis.  */
          return true;
        }

      if (stmt_order1 == stmt_order2)
        /* Slow check which is rare.  */
        return is_preceding_in_real_order (stmt1, stmt2);
      else
        return stmt_order1 < stmt_order2;
    }
  else
    {
      bool dominates = false;
      dominates = dominated_by_p (CDI_DOMINATORS, bb2, bb1);
      return dominates;
    }
}

/* expression of the form:
    a - b - c - d - e
  allows ressociation of operands b, c, d, and e.
  This requires left tree expansion only.
*/

static bool
is_reassociable_minus_op (enum tree_code rhs_code, tree rhs1)
{
  gimple def1;
  if (rhs_code != MINUS_EXPR)
    return false;

  if (TREE_CODE (rhs1) != SSA_NAME || !has_single_use (rhs1))
    return false;

  def1 = SSA_NAME_DEF_STMT (rhs1);
  if (is_gimple_assign (def1)
      && gimple_assign_rhs_code (def1) != MINUS_EXPR)
    return false;

  return true;
}

/* The function returns true if the right hand side operands RHS1 and RHS2
   are reassociable w.r.t to opcode RHS_CODE.  LHS is the left hand side 
   of the gimple assignment.  */

static inline bool
is_gimple_assign_rhs_reassociable (enum tree_code rhs_code,
				   tree lhs, tree rhs1, tree rhs2)
{

  if (!associative_tree_code (rhs_code)
      && !is_reassociable_minus_op (rhs_code, rhs1))
    return false;

  /* If associative-math we can do reassociation for
     non-integral types.  Or, we can do reassociation for
     non-saturating fixed-point types.  */

  if ((!INTEGRAL_TYPE_P (TREE_TYPE (lhs))
       || !INTEGRAL_TYPE_P (TREE_TYPE (rhs1))
       || !INTEGRAL_TYPE_P (TREE_TYPE (rhs2)))
      && (!SCALAR_FLOAT_TYPE_P (TREE_TYPE (lhs))
	  || !SCALAR_FLOAT_TYPE_P (TREE_TYPE(rhs1))
	  || !SCALAR_FLOAT_TYPE_P (TREE_TYPE(rhs2))
	  || !flag_associative_math)
      && (!NON_SAT_FIXED_POINT_TYPE_P (TREE_TYPE (lhs))
	  || !NON_SAT_FIXED_POINT_TYPE_P (TREE_TYPE(rhs1))
	  || !NON_SAT_FIXED_POINT_TYPE_P (TREE_TYPE(rhs2))))
    return false;

  return true;
}

/* The function expands the expression tree REASSOC_TREE by checking
   the tree operand at slot OPERAND_SLOT.  */

static void
expand_reassoc_tree (lrs_reassoc_tree_p reassoc_tree, treep operand_slot,
                     bool is_right_subtree, lrs_region_p region)
{
  gimple def_stmt;
  treep rhs1, rhs2;
  enum tree_code rhs_code;
  basic_block bb;
  int bb_rid;

  if (TREE_CODE (*operand_slot) != SSA_NAME)
    {
      VEC_safe_push (tree, heap, reassoc_tree->leaf_operands,
		     *operand_slot);
      VEC_safe_push (treep, heap, reassoc_tree->use_ref_slots,
		     operand_slot);
      return;
    }

  def_stmt = SSA_NAME_DEF_STMT (*operand_slot);
  if (!is_gimple_assign (def_stmt)
      || !has_single_use (*operand_slot))
    {
      VEC_safe_push (tree, heap, reassoc_tree->leaf_operands,
		     *operand_slot);
      VEC_safe_push (treep, heap, reassoc_tree->use_ref_slots,
		     operand_slot);
      return;
    }
  bb = gimple_bb (def_stmt);
  if (!get_bb_index_in_region (bb, region, &bb_rid))
    {
      VEC_safe_push (tree, heap, reassoc_tree->leaf_operands,
		     *operand_slot);
      VEC_safe_push (treep, heap, reassoc_tree->use_ref_slots,
		     operand_slot);
      return;
    }
  /* We limit the tree to one BB for now. When this is changed, we
     also need to change the logic in reassoc_tree_opnd_cmp.  */
  if (bb != gimple_bb (reassoc_tree->root))
    {
      VEC_safe_push (tree, heap, reassoc_tree->leaf_operands,
		     *operand_slot);
      VEC_safe_push (treep, heap, reassoc_tree->use_ref_slots,
		     operand_slot);
      return;
    }

  rhs_code = gimple_assign_rhs_code (def_stmt);
  if (rhs_code != reassoc_tree->opc ||
      (reassoc_tree->opc == MINUS_EXPR && is_right_subtree))
    {
      VEC_safe_push (tree, heap, reassoc_tree->leaf_operands,
		     *operand_slot);
      VEC_safe_push (treep, heap, reassoc_tree->use_ref_slots,
		     operand_slot);
      return;
    }

  rhs1 = gimple_assign_rhs1_ptr (def_stmt);
  rhs2 = gimple_assign_rhs2_ptr (def_stmt);
  gimple_set_visited (def_stmt, true);
  VEC_safe_push (gimple, heap, reassoc_tree->inner_nodes, def_stmt);

  expand_reassoc_tree (reassoc_tree, rhs1, false, region);
  expand_reassoc_tree (reassoc_tree, rhs2, true, region);
}

/* The function returns the expanded reassociation tree for expression
   rooted at ROOT_STMT.  RHS_CODE is the opcode of the gimple assignment
   right hand side.  RHS1 and RHS2 are the operand slots of ROOT_STMT.  */

static lrs_reassoc_tree_p
get_reassoc_tree(gimple root_stmt,
		 enum tree_code rhs_code,
		 treep rhs1, treep rhs2,
		 lrs_region_p region)
{
  lrs_reassoc_tree_p reassoc_tree;
  reassoc_tree
    = (lrs_reassoc_tree_p) pool_alloc (region->lrs_reassoc_tree_pool);
  VEC_safe_push (lrs_reassoc_tree_p, heap,
		 region->lrs_reassoc_trees, reassoc_tree);
  reassoc_tree->opc = rhs_code;
  reassoc_tree->root = root_stmt;
  reassoc_tree->inner_nodes = NULL;
  reassoc_tree->leaf_operands = NULL;
  reassoc_tree->use_ref_slots = NULL;
  VEC_safe_push (gimple, heap, reassoc_tree->inner_nodes,
		 root_stmt);
  gimple_set_visited (root_stmt, true);
  expand_reassoc_tree (reassoc_tree, rhs1, false, region);
  expand_reassoc_tree (reassoc_tree, rhs2, true, region);

  return reassoc_tree;
}

/* The comparison function is used in sorting reassociation tree's operands.
   The operands are sorted according to the order of their defining statements.  */

static basic_block cur_bb = NULL;
static int
reassoc_tree_opnd_cmp (const void *p1, const void *p2)
{
  tree opnd1, opnd2;
  enum tree_code tc1, tc2;

  opnd1 = *(const tree *) p1;
  opnd2 = *(const tree *) p2;
  if (opnd1 == opnd2)
    return 0;

  tc1 = TREE_CODE (opnd1);
  tc2 = TREE_CODE (opnd2);
  if (tc1 != SSA_NAME && tc2 == SSA_NAME)
    return -1;
  else if (tc1 == SSA_NAME && tc2 != SSA_NAME)
    return 1;
  else if (tc1 != SSA_NAME && tc2 != SSA_NAME)
    return SSA_NAME_VERSION (opnd1) - SSA_NAME_VERSION (opnd2);
  else
    {
      gimple stmt1, stmt2;
      basic_block bb1, bb2;

      stmt1 = SSA_NAME_DEF_STMT (opnd1);
      stmt2 = SSA_NAME_DEF_STMT (opnd2);
      bb1 = gimple_bb (stmt1);
      bb2 = gimple_bb (stmt2);

      /* Both statements are not in the current basic block, use SSA names'
	 DECL_UIDs and versions to determine order.  */
      if (bb1 != cur_bb && bb2 != cur_bb)
	{
	  tree v1 = SSA_NAME_VAR (opnd1);
	  tree v2 = SSA_NAME_VAR (opnd2);
	  if (v1 == v2)
	    return SSA_NAME_VERSION (opnd1) - SSA_NAME_VERSION (opnd2);
	  else
	    return DECL_UID (v1) - DECL_UID (v2);
	}

      if (bb1 != cur_bb)
        return -1;
      if (bb2 != cur_bb)
        return 1;
      return get_stmt_order (stmt1) - get_stmt_order (stmt2);
    }
}

/* The comparison function is used in sorting of the internal nodes
   of the reassociation tree.  */

static int
reassoc_inner_node_cmp (const void *p1, const void *p2)
{
  gimple node1, node2;

  node1 = *(const gimple *) p1;
  node2 = *(const gimple *) p2;

  return get_stmt_order (node1) - get_stmt_order (node2);
}


/* The function inserts the use refs from STMT into use ref vector
    USE_REFS.  OPND_SET is a pointer set of use refs.  */

static inline void
append_cur_use_refs (gimple stmt, VEC(treep, heap) **use_refs,
		     struct pointer_set_t * opnd_set)
{
  treep use_ref;

  use_ref = gimple_assign_rhs1_ptr (stmt);
  if (pointer_set_contains (opnd_set, *use_ref))
    VEC_safe_push (treep, heap, *use_refs, use_ref);
  use_ref = gimple_assign_rhs2_ptr (stmt);
  if (pointer_set_contains (opnd_set, *use_ref))
    VEC_safe_push (treep, heap, *use_refs, use_ref);
}

/* The function clears or sets the bits in bitmap BITVEC
   associated with use references in vector USE_REFS.
   VAL is a flag.  When it is non zero, the bits are
   set to 1, otherwise the bits are cleared.  */

static inline void
reset_use_ref_bits (VEC(treep, heap) *use_refs, int val,
		    sbitmap bitvec, lrs_region_p region)
{
  size_t i, n;
  n = VEC_length (treep, use_refs);

  for (i = 0; i < n; i++)
    {
      treep use_ref = VEC_index (treep, use_refs, i);
      int bit_pos;
      if (TREE_CODE (*use_ref) != SSA_NAME)
	continue;
      bit_pos = get_use_ref_bit_pos (use_ref, region);
      if (val)
	SET_BIT (bitvec, bit_pos);
      else
	RESET_BIT (bitvec, bit_pos);
    }
}

/* After operand reassociation, this function is used to remap
   operand slot to the new bit positions associated with
   the old operand slot holding the same value.  REASSOC_TREE
   is the tree that is reassociated, NEW_BIT_POS_MAP is the map
   from operand value to bit position.  */

static void
remap_use_ref_bit_pos (lrs_reassoc_tree_p reassoc_tree,
		       struct pointer_map_t *new_bit_pos_map,
		       lrs_region_p region)
{
  size_t i, n, s = 0;

  n = VEC_length (treep, reassoc_tree->use_ref_slots);

  for (i = s; i < n; i++)
    {
      void **slot;
      tree opnd;
      treep use_ref_slot = VEC_index (treep, reassoc_tree->use_ref_slots, i);

      opnd =  *use_ref_slot;
      slot = pointer_map_contains (new_bit_pos_map, opnd);
      gcc_assert (slot);
      if ((size_t) *slot != (size_t) -1)
        {
          int bit_pos = (long) *slot;
          set_use_ref_bit_pos (use_ref_slot, bit_pos, region);
        }
    }
}

/* The function updates the use-ref data flow result after reassociating
   tree REASSOC_TREE.  OPND_SET is the pointer set of operands.
   NEW_BIT_POS_MAP is the map from operand value to bit position, and REGION
   is the lrs region.  */

static void
update_dataflow_ur_for_reassoc (lrs_reassoc_tree_p reassoc_tree,
				struct pointer_set_t *opnd_set,
				struct pointer_map_t *new_bit_pos_map,
				lrs_region_p region)
{
  gimple_stmt_iterator gsi;
  gimple cur_stmt, prev_stmt, prev_stmt_in_tree;
  size_t n, cur_stmt_idx;
  VEC(treep, heap) *cur_use_refs = NULL;

  /* Remap bit positions  */
  remap_use_ref_bit_pos (reassoc_tree, new_bit_pos_map, region);

  n = VEC_length (gimple, reassoc_tree->inner_nodes);
  cur_stmt_idx = n - 1;

  while (cur_stmt_idx > 0)
    {
      sbitmap use_ref_bvec;
      cur_stmt = VEC_index (gimple, reassoc_tree->inner_nodes, cur_stmt_idx);
      prev_stmt_in_tree
          = VEC_index (gimple, reassoc_tree->inner_nodes, cur_stmt_idx - 1);
      append_cur_use_refs (cur_stmt, &cur_use_refs, opnd_set);
      gsi = gsi_for_stmt (cur_stmt);
      do
        {
          gsi_prev (&gsi);
          prev_stmt = gsi_stmt (gsi);
          use_ref_bvec = get_across_stmt_use_ref_set (prev_stmt, region);
          reset_use_ref_bits (reassoc_tree->use_ref_slots, 0, use_ref_bvec, region);
          reset_use_ref_bits (cur_use_refs, 1, use_ref_bvec, region);
        } while (prev_stmt != prev_stmt_in_tree);

      cur_stmt_idx--;
    }
}

/* The function performs statement update after reassociation of STMT.  */

static void
update_gimple_stmt (gimple stmt, lrs_region_p region)
{
  lrs_stmt_p norm_stmt;

  norm_stmt = get_normalized_gimple_stmt (stmt, region);
  free (norm_stmt->uses);
  norm_stmt->num_uses = 0;
  normalize_gimple_stmt (stmt, norm_stmt);

  /* Now ssa update.  */
  update_stmt (stmt);
}


static void
negate_opnds (void)
{
  size_t n, i;

  if (!pending_negates.opnds_to_negate)
    return;

  gcc_assert (VEC_length (tree, pending_negates.opnds_to_negate)
              == VEC_length (gimple, pending_negates.stmts_to_fixup));

  n = VEC_length (tree, pending_negates.opnds_to_negate);

  for (i = 0; i < n; i++)
    {
      tree negate_result;
      gimple_stmt_iterator gsi;
      gimple insert_point;
      bool insert_before;

      tree opnd_to_negate
          = VEC_index (tree, pending_negates.opnds_to_negate, i);
      gimple stmt_to_fixup
          = VEC_index (gimple, pending_negates.stmts_to_fixup, i);
      gcc_assert (opnd_to_negate == gimple_assign_rhs1 (stmt_to_fixup));
      if (TREE_CODE (opnd_to_negate) != SSA_NAME
          || gimple_code (SSA_NAME_DEF_STMT (opnd_to_negate)) == GIMPLE_PHI)
        {
          insert_before = true;
          insert_point = stmt_to_fixup;
        }
      else
        {
          insert_before = false;
          insert_point = SSA_NAME_DEF_STMT (opnd_to_negate);
          if (gimple_nop_p (insert_point))
            {
              insert_before = true;
              insert_point = stmt_to_fixup;
            }
        }

      gsi = gsi_for_stmt (insert_point);
      negate_result
          = fold_build1 (NEGATE_EXPR, TREE_TYPE (opnd_to_negate), opnd_to_negate);
      negate_result
          = force_gimple_operand_gsi (&gsi, negate_result, true,
                                      NULL_TREE, insert_before, GSI_SAME_STMT);
      gimple_assign_set_rhs1 (stmt_to_fixup, negate_result);
      update_stmt (stmt_to_fixup);
    }
}

/* The function performs reassociation for expression tree REASSOC_TREE in
   REGION.  After reassociation, more freedom (no dependence violations) is 
   created for code motions to reduce overlapping live ranges.

   Example:

   Before reassociation -- upward code motion (closes to their defs in (1)
   (2) and (3) ) of (4), (5), and (6) are not possible due to dependence 
   violation.  Downward motion of (1), (2), (3) (closest to their uses) is either
   imposible due to possible dependance between (1)/(2)/(3), or not profitable due
   to increased live times of their rhs LRs.

     x  = ...  (1)
     y  = ...  (2)
     z  = ...  (3)

     u = z + 1; (4)
     v = u + y; (5)
     w = v + x; (6)

   After Reassociation:

    x = ...  (1)
    y = ...  (2)
    z = ...  (3)

    u = x + 1;
    v = u + y;
    w = v + z;


   This allows code motion to produce the following code sequence:

    x = ...
    u = x + 1;
    y = ...
    v = u + y;
    z = ...
    w = v + z;
*/

static void
do_lrs_reassoc (lrs_reassoc_tree_p reassoc_tree, lrs_region_p region)
{
  size_t num_operands;
  size_t num_inner_nodes;
  gimple stmt;
  tree opnd, neg_opnd = NULL;
  struct pointer_set_t *opnd_set;
  struct pointer_map_t *new_bpos_map = NULL;
  size_t i, j;
  size_t min_tree;

  num_operands = VEC_length (tree, reassoc_tree->leaf_operands);
  num_inner_nodes = VEC_length (gimple, reassoc_tree->inner_nodes) ;
  gcc_assert (num_inner_nodes + 1 == num_operands);
  min_tree = PARAM_VALUE (PARAM_REG_PRESSURE_MIN_TREE_TO_RESHAPE);

  if (num_operands < min_tree)
    return;

  if (reassoc_tree->opc == MINUS_EXPR)
    neg_opnd = VEC_index (tree, reassoc_tree->leaf_operands, 0);

  cur_bb = gimple_bb (reassoc_tree->root);
  /* Sort the leaf operands.  The operand slots array is not sorted.  */
  qsort (VEC_address (tree, reassoc_tree->leaf_operands), num_operands,
         sizeof (tree), reassoc_tree_opnd_cmp);
  cur_bb = NULL;

  /* Sort the internal tree nodes.  */
  qsort (VEC_address (gimple, reassoc_tree->inner_nodes), num_operands - 1,
         sizeof (gimple), reassoc_inner_node_cmp);

  gcc_assert (VEC_index (gimple, reassoc_tree->inner_nodes, num_operands - 2)
	      == reassoc_tree->root);

  /* Now collect the pointer set of leaf operands.  */
  opnd_set = pointer_set_create ();
  for (i = 0; i < num_operands; i++)
    {
      opnd = VEC_index (tree, reassoc_tree->leaf_operands, i);
      pointer_set_insert (opnd_set, opnd);
    }

  /* Map the operand value to the bit position of the corresponding use-ref
     bit position before reassociation transformation.  The mapping is used to
     remap the new operand slot's bit positions.  */

  new_bpos_map = pointer_map_create ();
  for (i = 0; i < num_operands; i++)
    {
      void **slot;
      treep use_ref;
      tree val;
      long bit_pos;

      use_ref = VEC_index (treep, reassoc_tree->use_ref_slots, i);
      val = *use_ref;
      slot = pointer_map_insert (new_bpos_map, val);
      bit_pos = ((TREE_CODE (val) == SSA_NAME)
		 ? get_use_ref_bit_pos (use_ref, region): -1) ;
      *slot = (void *)bit_pos;
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "REASSOCITING:\n");
      print_lrs_reassoc_tree (dump_file, reassoc_tree);
      fprintf (dump_file, "INTO\n");
    }

  /* Now reaasign the leaf operands to the leaf operand slots.  */
  j = 0;
  for (i = 0; i < num_inner_nodes; i++)
    {
      tree orig_opnd;
      bool need_update = false;
      bool need_neg = (neg_opnd != NULL);

      stmt = VEC_index (gimple, reassoc_tree->inner_nodes, i);
      orig_opnd = gimple_assign_rhs1 (stmt);
      if (pointer_set_contains (opnd_set, orig_opnd))
	{
	  opnd = VEC_index (tree, reassoc_tree->leaf_operands, j++);
	  if (opnd != orig_opnd)
	    {
	      gimple_assign_set_rhs1 (stmt, opnd);
	      need_update = true;

              /* Negation handling */
              /* It is a left linearized tree -- only the first
                 operand can be the left operand.  */
              gcc_assert (!need_neg || orig_opnd == neg_opnd);
              /* insert negating statement.  */
              if (need_neg)
                {
                  VEC_safe_push (tree, heap,
                                 pending_negates.opnds_to_negate, opnd);
                  VEC_safe_push (gimple, heap,
                                 pending_negates.stmts_to_fixup, stmt);
                }
	    }
	}
      orig_opnd = gimple_assign_rhs2 (stmt);
      if (pointer_set_contains (opnd_set, orig_opnd))
	{
	  opnd = VEC_index (tree, reassoc_tree->leaf_operands, j++);
	  if (opnd != orig_opnd)
	    {
	      gimple_assign_set_rhs2 (stmt, opnd);
	      need_update = true;

              if (need_neg && opnd == neg_opnd)
                gimple_assign_set_rhs_code (stmt, PLUS_EXPR);
	    }
	}
      if (need_update)
	update_gimple_stmt (stmt, region);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    print_lrs_reassoc_tree (dump_file, reassoc_tree);

  gcc_assert (j == num_operands);

  update_dataflow_ur_for_reassoc (reassoc_tree, opnd_set, new_bpos_map, region);

  pointer_map_destroy (new_bpos_map);
  pointer_set_destroy (opnd_set);
}


/* The function performs reassociation on the expression
   tree rooted at statement STMT in REGION.  */

static void
do_lrs_shrink_by_reassoc (gimple stmt, lrs_region_p region)
{
  tree lhs, *rhs1, *rhs2;
  enum tree_code rhs_code;
  lrs_reassoc_tree_p reassoc_tree;

  if (gimple_visited_p (stmt))
    return;

  if (!is_gimple_assign (stmt))
    return;

  rhs_code = gimple_assign_rhs_code (stmt);

  if (get_gimple_rhs_class (rhs_code) != GIMPLE_BINARY_RHS)
    return;

  lhs = gimple_assign_lhs (stmt);
  rhs1 = gimple_assign_rhs1_ptr (stmt);
  rhs2 = gimple_assign_rhs2_ptr (stmt);

  if (!is_gimple_assign_rhs_reassociable (rhs_code,
					  lhs, *rhs1, *rhs2))
    return;

  reassoc_tree = get_reassoc_tree (stmt, rhs_code,
				   rhs1, rhs2, region);

  do_lrs_reassoc (reassoc_tree, region);
}


/* The function performs expression reassociation for 
   statements in REGION.  */

static void
shrink_lrs_reassociation (lrs_region_p region)
{
  size_t i;

  if (!do_reassoc ())
    return;

  region->lrs_reassoc_tree_pool
      = create_alloc_pool ("lrs linear tree pool",
                           sizeof (struct lrs_reassoc_tree), 50);

  for (i = 0; i < region->num_bbs; i++)
    {
      basic_block bb = region->body[i];
      gimple_stmt_iterator gsi; 
      for (gsi = gsi_last_bb (bb); !gsi_end_p (gsi); gsi_prev (&gsi))
	{
	  gimple stmt = gsi_stmt (gsi);
	  do_lrs_shrink_by_reassoc (stmt, region);
	}
    }
}

/* The function returns true if STMT has float typed constant
   operand.  */

static inline bool
has_float_typed_const_operand (gimple stmt)
{
  unsigned i, n;

  n = gimple_num_ops (stmt);
  for (i = 1; i < n; i++)
    {
      tree op = gimple_op (stmt, i);
      if (is_gimple_constant (op) 
          && FLOAT_TYPE_P (TREE_TYPE (op)))
        return true;
    }
  return false;
}

/* The function returns true if STMT is selected as
   candidate for upward code motion.  */

static bool
is_upward_motion_candidate (gimple stmt)
{
  if (!is_gimple_assign (stmt) )
    return false;

  if (!ZERO_SSA_OPERANDS (stmt, SSA_OP_ALL_VIRTUALS))
    return false;

  if (has_float_typed_const_operand (stmt))
    return false;

  return true;
}


/* The function computes the number of LRs that are not live after
   statement NORM_STMT (with id STMT_ID) in REGION.  *NGR is the 
   number GRs that are not live across, and *NFR is the number of FRs 
   that are not live across.  The number of gr uses is in *NGR_USE, and
   *NFR_USE is the number of fr uses.  */

static void
get_num_lrs_not_live_across (lrs_stmt_p norm_stmt, int stmt_id,
                             sbitmap use_ref_set, lrs_region_p region,
                             int *ngr, int *nfr, int *ngr_use, int *nfr_use)
{
  size_t i;

  *ngr = 0;
  *nfr = 0;
  *ngr_use = 0;
  *nfr_use = 0;

  if (norm_stmt->num_uses == 0)
    return;

  if (use_ref_set == NULL)
    use_ref_set = region->across_stmt_use_ref_sets[stmt_id];

  for (i = 0; i < norm_stmt->num_uses; i++)
    {
      bool is_live_across = true;
      size_t first_bit, last_bit;
      tree *use = norm_stmt->uses[i];

      get_def_bit_range (&first_bit, &last_bit, *use, region);
      if (sbitmap_range_empty_p (use_ref_set, first_bit,
                                 last_bit - first_bit + 1))
        is_live_across = false;

      if (get_nm_reg_class (*use) == lrc_gr)
	{
	  (*ngr_use)++;
	  if (!is_live_across)
	    (*ngr)++;
	}
      else
	{
	  (*nfr_use)++;
	  if (!is_live_across)
	    (*nfr)++;
	}
    }
}

/* The function computes the number of GR defs (returned in *D_GR), 
   and the number of FR defs (in *D_FR) in statement NORM_STMT.  */

static inline void
get_num_lrs_defed_by (lrs_stmt_p norm_stmt, int *d_gr, int *d_fr)
{
  *d_gr = 0;
  *d_fr = 0;

  if (norm_stmt->def)
    {
      if (get_nm_reg_class (norm_stmt->def) == lrc_gr)
        (*d_gr)++;
      else
        (*d_fr)++;
    }
}

/* The function computes the register pressure changes in the program
   point between the STMT1 and STMT2 if two statements are swapped.
   STMT1 precedes STMT2 in the code stream.  The result will be stored
   into the output parameter *GR_CHANGE and *FR_CHANGE.  A positive value
   indicates regiter pressure reduction.  REGION is the code region where
   the optimization is performed.

   The formular for computing the register pressure change (reduction) is:

   reg_pressure_change (stmt1, stmt2, reg_class)
      = num_of_lrs_not_live_across (stmt2, reg_class)
        * num_lrs_defined (stmt1, reg_class)
      - num_of_lrs_not_live_across (stmtl, reg_class)
        * num_lrs_defined (stmt2, reg_class)


   More precisely, num_of_lrs_not_live_across (stmt1, reg_class) should
   actually be the number of LRs referenced in stmt1 that is not live across
   stmt2.  For instance:

   stmt1:  a = b    + c
   stmt2:  x = b(N) + y;

   The reference of b in stmt2 is the last reference -- so b is live across stmt1,
   but not live across stmt2.  However if stmt1 and stmt2 is swapped, new interference
   will be introduced between x and b.

   There are three program points related to the two statements that are to
   be swapped, and register pressure in the program points before and after
   the two statements do not change.

   In the following examples, LRs that do not live across the statement are
   marked with (N).  Program points are Pnn:, and live LRs are in curly braces.

   Example 1: register pressure is reduced after swapping:

   Before code motion
   ------------------

    P1: {w, v, y, z},    reg_pressure = 4
      u = w + v;
    P2: {u, w, v, y, z}, reg_pressure = 5
      x = y + z(N);
    P3: {u, x, w, v, y}, reg_pressure = 5

   After code motion
   ----------------- 

    P1: {w, v, y, z},    reg_pressure = 4
      x = y + z(N);
    P2: {x, y, w, v},    reg_pressure = 4
      u = w + v;
    P3: {u, x, w, v, y}, reg_pressure = 5



   Example 2: register pressure is reduced after swapping:

   Before code motion
   ------------------

    P1: {w, v, y, z},    reg_pressure = 4
      u = w + v;
    P2: {u, w, v, y, z}, reg_pressure = 5
      -- = y + z(N);
    P3: {u, w, v, y},    reg_pressure = 4

   After code motion
   ----------------- 

    P1: {w, v, y, z},    reg_pressure = 4
     -- = y + z(N);
    P2: { y, w, v},      reg_pressure = 3
      u = w + v;
    P3: {u, w, v, y},    reg_pressure = 4


   Example 3: register pressure does not change after swapping:

   Before code motion
   ------------------

    P1: {w, v, y, z},    reg_pressure = 4
      u = w(N) + v;
    P2: {u, v, y, z},    reg_pressure = 4
      x = y + z(N);
    P3: {x, u, v, y},    reg_pressure = 4

   After code motion
   ----------------- 

    P1: {w, v, y, z},    reg_pressure = 4
      x = y + z(N);
    P2: {x, y, w, v},    reg_pressure = 4
      u = w(N) + v;
    P3: {x, u, v, y},    reg_pressure = 4

   Example 4: register pressure is reduced after swapping:

   Before code motion
   ------------------

    P1: {w, v, y, z},    reg_pressure = 4
      u = w + v;
    P2: {u, w, v, y, z}, reg_pressure = 5
      x = y(N) + z(N);
    P3: {x, u, w, v},    reg_pressure = 4

   After code motion
   -----------------

    P1: {w, v, y, z},    reg_pressure = 4
      x = y(N) + z(N);
    P2: {x, w, v},       reg_pressure = 3
      u = w + v;
    P3: {x, u, w, v},    reg_pressure = 4

  Example 4: register pressure is increased after swapping:

   Before code motion
   ------------------

    P1: {w, v, y, z},    reg_pressure = 4
      -- = w(N) + v;
    P2: { v, y, z},      reg_pressure = 3
      x = y + z;
    P3: {x, v, y, z},    reg_pressure = 4

   After code motion
   -----------------

    P1: {w, v, y, z},    reg_pressure = 4
      x = y + z;
    P2: {x, y, z, w, v}, reg_pressure = 5
      - = w(N) + v;
    P3: {x, v, y, z},    reg_pressure = 4

*/

static void
get_reg_pressure_change_if_swapped (int stmt_id1, lrs_stmt_p norm_stmt1,
                                    int stmt_id2, lrs_stmt_p norm_stmt2,
                                    sbitmap stmt2_use_ref_set,
                                    lrs_region_p region,
                                    int *gr_change, int *fr_change)

{
  int non_live_across_gr1, non_live_across_fr1;
  int non_live_across_gr2, non_live_across_fr2;
  int ngr_def1, nfr_def1;
  int ngr_def2, nfr_def2;
  int ngr_use1, nfr_use1;
  int ngr_use2, nfr_use2;

  get_num_lrs_not_live_across (norm_stmt1, stmt_id1,
                               stmt2_use_ref_set, region,
                               &non_live_across_gr1,
                               &non_live_across_fr1,
			       &ngr_use1, &nfr_use1);

  get_num_lrs_not_live_across (norm_stmt2, stmt_id2,
                               stmt2_use_ref_set, region,
                               &non_live_across_gr2,
                               &non_live_across_fr2,
			       &ngr_use2, &nfr_use2);

  get_num_lrs_defed_by (norm_stmt1, &ngr_def1, &nfr_def1);
  get_num_lrs_defed_by (norm_stmt2, &ngr_def2, &nfr_def2);


  *gr_change = (non_live_across_gr2 * ngr_def1
                - non_live_across_gr1 * ngr_def2);

  *fr_change = (non_live_across_fr2 * nfr_def1
                - non_live_across_fr1 * nfr_def2);
}

/*  STMT is a candidate for updward code motion.  The function computes
   the earliest insertion point for the code motion.  EARLIEST_STMT is the
   earliest statement in the same bb where STMT can be moved across (inserted
   before).  *INSERT_POINT is the earliest possible statement STMT can be
   inserted before without increasing register pressure.
   If no such insertion point can be found, *INSERT_POINT  is set to NULL.  */

static void
compute_earliest_insertion_point (gimple stmt, gimple earliest_stmt,
                                  lrs_region_p region,
                                  gimple *insert_point)
{
  gimple_stmt_iterator gsi;
  gimple best_target_loc = NULL;
  gimple cur_stmt;
  int tot_reg_reduc = 0, max_reg_reduc = 0;
  int tot_gr_reduc = 0, max_gr_reduc = 0;
  int tot_fr_reduc = 0, max_fr_reduc = 0;
  sbitmap stmt_use_ref_set = NULL;
  int stmt_id;
  lrs_stmt_p norm_stmt;

  gsi = gsi_for_stmt (stmt);
  gsi_prev (&gsi);
  stmt_use_ref_set = sbitmap_alloc (region->bitvec_width);
  stmt_id = get_stmt_idx_in_region (stmt);
  norm_stmt = get_normalized_gimple_stmt (stmt, region);
  sbitmap_copy (stmt_use_ref_set, region->across_stmt_use_ref_sets[stmt_id]);

  do
  {
    int cur_stmt_id;
    lrs_stmt_p cur_norm_stmt;
    int gr_reg_cg = 0;
    int fr_reg_cg = 0;
    size_t i, n;

    cur_stmt = gsi_stmt (gsi);
    cur_stmt_id = get_stmt_idx_in_region (cur_stmt);
    cur_norm_stmt = get_normalized_gimple_stmt (cur_stmt, region);
    get_reg_pressure_change_if_swapped (cur_stmt_id, cur_norm_stmt,
                                        stmt_id, norm_stmt,
                                        stmt_use_ref_set, region,
                                        &gr_reg_cg, &fr_reg_cg);

    tot_reg_reduc += gr_reg_cg;
    tot_reg_reduc += fr_reg_cg;
    tot_gr_reduc += gr_reg_cg;
    tot_fr_reduc += fr_reg_cg;

    if (tot_reg_reduc >= max_reg_reduc)
      {
        max_reg_reduc = tot_reg_reduc;
        best_target_loc = cur_stmt;
      }

    if (tot_gr_reduc >= max_gr_reduc)
      max_gr_reduc = tot_gr_reduc;
    if (tot_fr_reduc >= max_fr_reduc)
      max_fr_reduc = tot_fr_reduc;

    /* Now update the use-ref set for stmt as if it is moved across (up)
       cur_stmt.  */

    n = cur_norm_stmt->num_uses;
    for (i = 0; i < n; i++)
      {
        int bit_pos;
        tree *use = cur_norm_stmt->uses[i];
        bit_pos = get_use_ref_bit_pos (use, region);
        SET_BIT (stmt_use_ref_set, bit_pos);
      }
    if (cur_norm_stmt->def)
      {
        size_t fbit, lbit;
        get_def_bit_range (&fbit, &lbit, cur_norm_stmt->def, region);
        for (i = fbit; i <= lbit; i++)
          RESET_BIT (stmt_use_ref_set, i);
      }

    gsi_prev (&gsi);
  } while (cur_stmt != earliest_stmt);

  if (max_reg_reduc > 0)
    *insert_point = best_target_loc;
  else
    *insert_point = NULL;

  sbitmap_free (stmt_use_ref_set);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "[CHECKING CODE MOTION]:\n");
      fprintf (dump_file, "\t[FROM] : ");
      print_gimple_stmt (dump_file, stmt, 0, 0);
      fprintf (dump_file, "\t[TO] : ");
      print_gimple_stmt (dump_file, earliest_stmt, 0, 0);
      fprintf (dump_file, "\t[RESULT]:\n");
      fprintf (dump_file, "\t[BEST TARGET] : ");
      if (*insert_point)
        print_gimple_stmt (dump_file, *insert_point, 0, 0);
      else
        fprintf (dump_file, "NO LOC \n");
      fprintf (dump_file, 
               "\tREG pressure reduction TOT : %d, MAX : %d\n",
               tot_reg_reduc, max_reg_reduc);
      fprintf (dump_file, 
               "\tGR pressure reduction TOT : %d, MAX : %d\n",
               tot_gr_reduc, max_gr_reduc);
      fprintf (dump_file, 
               "\tFR pressure reduction TOT : %d, MAX : %d\n",
               tot_fr_reduc, max_fr_reduc);

    }
}

/* The function computes the cost and savings in terms of
   register pressure reductions if STMT_TO_MOVE is moved to
   TARGET_LOC  (inserted before if IS_BEFORE is true and afer 
   if IS_BEFORE is false).  The cost of the upward code motion 
   is approximited by the total number of new interferences 
   that will be introduced and the savings is approximated by 
   the total number interferences that can be eliminated when 
   the code motion happens.  The function returns the gimple 
   statement before which STMT_TO_MOVE can be inserted or NULL
   if no profitable location can be found.  */

static gimple
check_upward_motion_profitability (gimple target_loc,
                                   gimple stmt_to_move,
                                   bool is_before,
                                   lrs_region_p region)
{
  gimple_stmt_iterator gsi;
  gimple adjusted_target_loc = NULL;

  basic_block bb = gimple_bb (target_loc);

  /* Only handle this for now.  */
  gcc_assert (gimple_bb (stmt_to_move) == bb);

  gsi = gsi_for_stmt (target_loc);
  if (!is_before)
    {
      gsi_next (&gsi);
      target_loc = gsi_stmt (gsi);
    }

  if (target_loc == stmt_to_move)
    return NULL;

  compute_earliest_insertion_point (stmt_to_move, target_loc,
                                    region, &adjusted_target_loc);

  return adjusted_target_loc;
}

/* This function adjusts the insertion point TARGET for
   the statement to be move ME and returns the new insertion
   point or NULL if no insertion point is appropriate.
   *INSERT_BEFORE is a flag indicating if the new insertion point
   is before or after returned gimple statement.  The client of
   this interface is responsible to set the initial value
   of the flag.  */

static gimple
check_move_target_loc (gimple target, gimple me, bool *insert_before)
{
  basic_block target_bb = 0;
  basic_block me_bb = 0;
  gimple_stmt_iterator gsi;
  gimple last_label = 0;

  /* Bail if the target stmt is a call with EH.  */
  if (stmt_ends_bb_p (target) && !*insert_before)
    return 0;

  if (gimple_code (target) == GIMPLE_PHI)
    {
      basic_block bb = gimple_bb (target);
      gsi = gsi_start_bb (bb);
      if (gsi_end_p (gsi))
        return 0;

      target = gsi_stmt (gsi);
      *insert_before = true;
    }
  else
    gsi = gsi_for_stmt (target);

  while (gimple_code (target) == GIMPLE_LABEL)
    {
      last_label = target;
      gsi_next (&gsi);
      if (gsi_end_p (gsi))
        break;
      target = gsi_stmt (gsi);
    }

  if (last_label)
    {
      *insert_before = false;
      target = last_label;
    }

  /* We do not really want to introduce redundancy nor do we need
     to do LIM here.  */

  target_bb = gimple_bb (target);
  me_bb = gimple_bb (me);

  if (target_bb->loop_father != me_bb->loop_father 
      || !dominated_by_p (CDI_POST_DOMINATORS, target_bb, me_bb))
    {
      *insert_before = true;
      return check_move_target_loc (gsi_stmt (gsi_start_bb (me_bb)),
                                    me, insert_before);
    }

  /* Do not handle this for now.  */
  if  (me_bb != target_bb)
    {
      *insert_before = true;
      return check_move_target_loc (gsi_stmt (gsi_start_bb (me_bb)),
                                    me, insert_before);
    }

  return target;
}

/* The function returns the defining statement for SSAVAR if
   it is dominated by CUR_LATEST.  Otherwise CUR_LATEST is returned.  */

static gimple
get_cur_latest_def (tree ssavar, gimple cur_latest)
{
  gimple cur_def = 0;
  cur_def = SSA_NAME_DEF_STMT (ssavar);

  if (cur_def && gimple_nop_p (cur_def))
    cur_def = 0;

  if (!cur_def)
    return cur_latest;

  if (!cur_latest)
    return cur_def;

  if (is_dominating (cur_latest, cur_def))
    return cur_def;

  return cur_latest;
}

/* The function returns the closest defining statement for 
   all the used rhs operands of STMT.  This function is only
   used by the upward code motion transformation in which
   statements with VUSES are not candidates, so VUSES are 
   not examined here.  See also is_upward_motion_candidate. 
   REGION is the code region being optimized.  */

static gimple
get_closest_def (gimple stmt, lrs_region_p region)
{
  int i, n;
  lrs_stmt_p norm_stmt;
  gimple cur_latest_def = 0;

  norm_stmt = get_normalized_gimple_stmt (stmt, region);

  n = norm_stmt->num_uses;
  for (i = 0; i < n; i++)
    {
      tree *op = norm_stmt->uses[i];
      cur_latest_def = get_cur_latest_def (*op, cur_latest_def);
    }

  if (!cur_latest_def)
    {
      gimple_stmt_iterator gsi0
          = gsi_start_bb (single_succ (ENTRY_BLOCK_PTR));
      cur_latest_def
          = gsi_end_p (gsi0)? 0 : gsi_stmt (gsi0);
    }

  return cur_latest_def;
}

/* The function updates the use-ref data flow information for all
   statements in the region enclosed by [FIRST_STMT_GSI, END_STMT_GSI)
   as well as the bitvector for the statement that is moved :
   MOVED_STMT_GSI.  The region is REGION.  */

static void
update_data_flow (gimple_stmt_iterator moved_stmt_gsi,
                  gimple_stmt_iterator first_stmt_gsi,
                  gimple_stmt_iterator end_stmt_gsi,
                  lrs_region_p region)
{
  gimple_stmt_iterator gsi;
  gimple_stmt_iterator gsi_prev_stmt;
  gimple moved_stmt;
  gimple first_stmt;
  gimple curr_stmt;
  gimple prev_stmt;
  gimple end_stmt;
  lrs_stmt_p norm_moved_stmt;
  sbitmap live_across_curr;
  sbitmap live_across_moved;
  sbitmap live_across_prev;
  size_t i, n, fbit, lbit;

  moved_stmt = gsi_stmt (moved_stmt_gsi);
  norm_moved_stmt = get_normalized_gimple_stmt (moved_stmt, region);
  n = norm_moved_stmt->num_uses;
  get_def_bit_range (&fbit, &lbit, norm_moved_stmt->def, region);
  live_across_moved
      = get_across_stmt_use_ref_set (moved_stmt, region);

  if (gsi_end_p (end_stmt_gsi))
    end_stmt = NULL;
  else
    end_stmt = gsi_stmt (end_stmt_gsi);

  gsi = first_stmt_gsi;
  curr_stmt = gsi_stmt (gsi);
  do
    {
      live_across_curr
          = get_across_stmt_use_ref_set (curr_stmt, region);
      for (i = 0; i < n; i++)
        {
          int bit_pos;
          tree *use = norm_moved_stmt->uses[i];
          bit_pos = get_use_ref_bit_pos (use, region);
          RESET_BIT (live_across_curr, bit_pos);
        }

      if (norm_moved_stmt->def)
        {
          for (i = fbit; i <= lbit; i++)
            SET_BIT (live_across_curr, i);
        }

      gsi_next (&gsi);
      curr_stmt = (gsi_end_p (gsi) ? NULL : gsi_stmt (gsi));

    } while (curr_stmt != end_stmt);

  /* Now update the live across set for the statement
     that is moved.  */

  gsi_prev_stmt = moved_stmt_gsi;
  gsi_prev (&gsi_prev_stmt);
  if (gsi_end_p (gsi_prev_stmt))
    prev_stmt = NULL;
  else
    prev_stmt = gsi_stmt (gsi_prev_stmt);
  if (prev_stmt)
    live_across_prev
        = get_across_stmt_use_ref_set (prev_stmt, region);
  else
    {
      int bidx = 0;
      basic_block bb = gimple_bb (moved_stmt);
      get_bb_index_in_region (bb, region, &bidx);
      live_across_prev
          = get_bb_use_ref_in_set (bidx, region);
    }

  sbitmap_copy (live_across_moved, live_across_prev);

  /* Now the final adjustment  */

  for (i = 0; i < n; i++)
    {
      int bit_pos;
      tree *use = norm_moved_stmt->uses[i];
      bit_pos = get_use_ref_bit_pos (use, region);
      RESET_BIT (live_across_moved, bit_pos);
    }
  if (norm_moved_stmt->def)
    {
      for (i = fbit; i <= lbit; i++)
        SET_BIT (live_across_moved, i);
    }

  /* Now update the order for the statement that
     is just moved -- it gets the same order as the
     statement it is inserted after/before.  */
  first_stmt = gsi_stmt (first_stmt_gsi);
  reset_stmt_order (moved_stmt, get_stmt_order (first_stmt));
}

/* The function performs code motion for the statement
   pointed to by GSI_CM_STMT and returns the iterator to
   the next statement before the code motion.  */

static gimple_stmt_iterator
do_lr_shrink_by_use_hoisting (gimple_stmt_iterator gsi_cm_stmt, 
                              lrs_region_p region)
{
  gimple cm_stmt, earliest;
  gimple_stmt_iterator gsi_next_stmt;
  gimple_stmt_iterator gsi_earliest;

  bool insert_before = false;

  cm_stmt = gsi_stmt (gsi_cm_stmt);
  gsi_next_stmt = gsi_cm_stmt;
  gsi_next (&gsi_next_stmt);

  if (!is_upward_motion_candidate (cm_stmt))
    return gsi_next_stmt;

  earliest = get_closest_def (cm_stmt, region);

  if (!earliest)
    return gsi_next_stmt;

  insert_before = false;
  earliest = check_move_target_loc (earliest, cm_stmt, &insert_before);

  if (!earliest || earliest == cm_stmt)
    return gsi_next_stmt;

  earliest = check_upward_motion_profitability (earliest, cm_stmt, 
                                                insert_before, region);
  if (earliest == NULL)
    return gsi_next_stmt;

  if (!dbg_cnt (lrs))
    return gsi_next_stmt;

  gsi_earliest = gsi_for_stmt (earliest);

  /* The insertion point is adjusted by is_upwared_motion_beneficial
     such that it is before earliest.  */
  gsi_move_before (&gsi_cm_stmt, &gsi_earliest);

  update_data_flow (gsi_for_stmt (cm_stmt), 
                    gsi_for_stmt (earliest),
                    gsi_next_stmt, region);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Moved UP\n");
      print_gimple_stmt (dump_file, cm_stmt, 0, 0);
      fprintf (dump_file, "just before \n");
      print_gimple_stmt (dump_file, earliest, 0, 0);
      fprintf (dump_file, "\n");
    }

  return gsi_next_stmt;
}


/* The function attempts to reduce the number of
   overlapping live ranges in BB by performing
   upward code motion for statements.  */

static void
shrink_lrs_up_motion (lrs_region_p region)
{
  size_t i;

  if (!do_upward_motion ())
    return;

  for (i = 0; i < region->num_bbs; i++)
    {
      basic_block bb = region->body[i];
      gimple_stmt_iterator gsi = gsi_start_bb (bb);
      while (!gsi_end_p (gsi))
        gsi = do_lr_shrink_by_use_hoisting (gsi, region);
    }

  dump_data_flow_result (region, "After upward motion");
}


/* This is the comparison function for sorting all uses
   of a definition.  The sorting is based on the order of 
   the use statements in the basic block.  Sorting is to 
   allow closest use to be easily found.  Note that the 
   BB of the use in a phi operand  is in the src bb of 
   the associatied edge.  */

static int
use_stmt_pos_cmp (const void *p1, const void *p2)
{
  basic_block b1, b2;
  gimple s1, s2, phi, s;
  use_operand_p phi_use, use;
  enum gimple_code c1, c2;
  int idx;
  edge use_edge;
  const use_operand_p u1 = *(const use_operand_p *)p1;
  const use_operand_p u2 = *(const use_operand_p *)p2;
  ssa_op_iter iter;

  gcc_assert(u1 != u2);

  s1 = USE_STMT (u1);
  s2 = USE_STMT (u2);
  c1 = gimple_code (s1);
  c2 = gimple_code (s2);

  if (c1 != GIMPLE_PHI && c2 != GIMPLE_PHI)
    {
      if (is_dominating (s1, s2))
        return -1;
      else if (is_dominating (s2, s1))
        return 1;

      b1 = gimple_bb (s1);
      b2 = gimple_bb (s2);

      if (b2->index != b1->index)
        return b2->index - b1->index;

      /* Uses occur in the same basic block.  */
      if (s1 == s2)
	{
	  /* The uses appear in the same statement, use positions to
 	     determine order.  We cannot order by SSA names because they
	     can refer to the same SSA name.  */
	  FOR_EACH_SSA_USE_OPERAND (use, s1, iter, SSA_OP_USE)
	    {
	      if (use == u1)
		return -1;
	      if (use == u2)
		return 1;
	    }
	  gcc_unreachable();
	}
      else
	{
	  /* This cannot happen.  */
	  gcc_unreachable();
	}
    }

  if (c1 == GIMPLE_PHI && c2 == GIMPLE_PHI)
    {
      if (gimple_bb (s2)->index - gimple_bb (s1)->index)
        return gimple_bb (s2)->index - gimple_bb (s1)->index;

      if (s1 == s2)
	{
	  /* The uses appear in the same PHI, use positions to
 	     determine order.  We cannot order by SSA names because they
	     can refer to the same SSA name.  */
	  gcc_assert(PHI_ARG_INDEX_FROM_USE (u1) - PHI_ARG_INDEX_FROM_USE (u2));
	  return PHI_ARG_INDEX_FROM_USE (u1) - PHI_ARG_INDEX_FROM_USE (u2);
	}
      else
	{
	  tree result1 = gimple_phi_result (s1);
	  tree result2 = gimple_phi_result (s2);
	  tree var1 = SSA_NAME_VAR (result1);
	  tree var2 = SSA_NAME_VAR (result2);

	  if (var1 == var2)
	    return SSA_NAME_VERSION (result2) - SSA_NAME_VERSION (result1);
	  else
	    return DECL_UID (var2) - DECL_UID (var1);
	}
    }

  if (c1 == GIMPLE_PHI)
    {
      phi = s1;
      phi_use = u1;
      s = s2;
    }
  else
    {
      phi = s2;
      phi_use = u2;
      s = s1;
    }

  idx = PHI_ARG_INDEX_FROM_USE (phi_use);
  use_edge = gimple_phi_arg_edge (phi, idx);

  b1 = gimple_bb (s);
  b2 = use_edge->src;

  if (b1 == b2 || dominated_by_p (CDI_DOMINATORS, b2, b1))
    {
      if (s == s1)
        return -1;
      else
        return 1;
    }

  return b2->index - b1->index;
}


DEF_VEC_P(use_operand_p);
DEF_VEC_ALLOC_P(use_operand_p, heap);

/* The function returns the closest use statement of STMT's
   definitions that also dominate all other uses.  STMT should 
   be a gimple assignment.  REGION is the code region under 
   optimization.  */

static gimple
get_closest_use (gimple stmt)
{
  int i, n;
  gimple closest_use = 0;
  use_operand_p use_p;
  imm_use_iterator iter;
  VEC(use_operand_p, heap) *uses = NULL;
  bool is_phi;
  basic_block bb1;

  tree nm = gimple_assign_lhs (stmt);

  FOR_EACH_IMM_USE_FAST (use_p, iter, nm)
    VEC_safe_push (use_operand_p, heap, uses, use_p);

  n = VEC_length (use_operand_p, uses);
  if (!n)
    return NULL;

  if (n == 1)
    return VEC_index (use_operand_p, uses, 0)->loc.stmt;

  qsort (VEC_address (use_operand_p, uses), n,
         sizeof (use_operand_p), use_stmt_pos_cmp);

  closest_use = VEC_index (use_operand_p, uses, 0)->loc.stmt;
  is_phi = (gimple_code (closest_use) == GIMPLE_PHI);
  if (is_phi && n > 1)
    return NULL;

  bb1 = gimple_bb (closest_use);
  for (i = 1; i < n; i++)
    {
      gimple cur_use_stmt;
      use_operand_p use = VEC_index (use_operand_p, uses, i);
      cur_use_stmt = use->loc.stmt;
      if (gimple_code (cur_use_stmt) == GIMPLE_PHI)
        {
          int idx;
          edge use_edge;

          idx = PHI_ARG_INDEX_FROM_USE (use);
          use_edge = gimple_phi_arg_edge (cur_use_stmt, idx);
          if (bb1 != use_edge->src 
              && !dominated_by_p (CDI_DOMINATORS, use_edge->src, bb1))
            return NULL;
        }
      else if (!is_dominating (closest_use, cur_use_stmt))
        return NULL;
    }

  return closest_use;
}

/* The function examine the downward code motion target location TARGET,
   and returns the adjusted location.  ME is the statement to be moved.
   If the insertion point is after the adjusted location, *INSERT_AFTER is
   set to true.  */

static gimple
check_down_motion_target_loc (gimple target, gimple me, 
                              bool *insert_after, lrs_region_p region)
{
  basic_block target_bb = 0;
  basic_block me_bb = 0;
  int target_bb_rid = -1;

  gcc_assert (gimple_code (target) != GIMPLE_LABEL);

  if (gimple_code (target) == GIMPLE_PHI)
    {
      /* we have to scan the phi operand to find the matching
         edge.  If multiple operands in the phi uses the same def, 
         then the phi would not be chosen as an insertion point --
         see get_closest_use.  */
      int i, n;
      bool found = false;
      tree def = gimple_assign_lhs (me);
      n = gimple_phi_num_args (target);
      for (i = 0; i < n; i++)
        {
          if (gimple_phi_arg_def (target, i) == def)
            {
              edge e;
              gimple_stmt_iterator target_gsi;
              found = true;
              e = gimple_phi_arg_edge (target, i);
              target_bb = e->src;
              target_gsi = gsi_last_bb (target_bb);
              *insert_after = true;
              target = gsi_stmt (target_gsi);
              break;
            }
        }
      gcc_assert (found);
      if (!target)
        return NULL;
      /* fall through for the rest the adjustment.  */
    }

  if (gimple_code (target) == GIMPLE_PHI 
      || gimple_code (target) == GIMPLE_LABEL)
    return NULL;

  /* move before the target stmt if it is a call with EH.  */
  if (stmt_ends_bb_p (target) && *insert_after)
    *insert_after = false;

  target_bb = gimple_bb (target);
  me_bb = gimple_bb (me);

  if (!get_bb_index_in_region (target_bb, region, &target_bb_rid)
      || !dominated_by_p (CDI_DOMINATORS, target_bb, me_bb))
    {
      *insert_after = true;
      return check_down_motion_target_loc (gsi_stmt (gsi_last_bb (me_bb)),
                                           me, insert_after, region);
    }

  return target;
}

/* Return the bitvector of reaching VDEFS at the program point
   before (when IS_AFTER is false) or after (when IS_AFTER is true)
   the TARGET_LOC statement.  */

static sbitmap
get_reaching_vdefs (gimple target_loc, bool is_after,
                    lrs_region_p region)
{
  sbitmap reaching_defs;

  if (!is_after)
    reaching_defs = get_stmt_rd_set (target_loc, region);
  else
    {
      gimple_stmt_iterator gsi = gsi_for_stmt (target_loc);
      gsi_next (&gsi);
      if (!gsi_end_p (gsi))
        {
          gimple nstmt = gsi_stmt (gsi);
          reaching_defs = get_stmt_rd_set (nstmt, region);
        }
      else
        {
          int rid = 0;
          basic_block bb = gimple_bb (target_loc);
          get_bb_index_in_region (bb, region, &rid);
          reaching_defs = get_bb_rd_out_set (rid, region);
        }
    }
  return reaching_defs;
}

/* Stack layout in cfgexpand.c performs stack reuse/overlay on
   stack variables that do not conflict. However variable conflicit
   computation is not based on variable life time overlap analsysis,
   but on information of variable scopes -- a variable conflicts with
   another variable in the same scope or a nested scope. Two variables
   won't conflict if they are in different scopes not nested with each
   other. The assumption is that no optimization will introduce life time
   overlap for stack variables in different scopes.  Return true if
   STMT_TO_MOVE reference a stack variable that may be a candidate for
   stack reuse. */
static bool
reference_overlapable_stack_variable_p (gimple stmt_to_move)
{
  enum tree_code gc;
  tree var;

  gcc_assert (is_gimple_assign (stmt_to_move));
  gc = gimple_assign_rhs_code (stmt_to_move);
  /* We do not care about PARM_DECL as they are in the top level scope.
     Should probably also filter out top level local VAR_DECLS.  */
  if (gc != VAR_DECL)
    return false;

  var = gimple_assign_rhs1 (stmt_to_move);

  if (TREE_STATIC (var) || DECL_EXTERNAL (var))
    return false;

  if (DECL_ARTIFICIAL (var))
    return false;

  return true;
}

/* The function checks to see if there are possible violations 
   of anti-depedency (memory) with this move.  Returns true if 
   there is none.  TARGET_LOC is the statement before/after which 
   statement STMT_TO_MOVE is to be moved.  IS_AFTER is the flag.  If
   it is true, the insertion point is after TARGET LOC, otherwise
   it is before it.  */

static bool
is_down_motion_legal (gimple target_loc, gimple stmt_to_move,
                      bool is_after, lrs_region_p region)
{
  sbitmap reaching_defs;
  struct voptype_d *vuses;
  int i, n;

  gcc_assert (!gimple_vdef_ops (stmt_to_move));

  if (!(vuses = gimple_vuse_ops (stmt_to_move)))
    return true;

  if (reference_overlapable_stack_variable_p (stmt_to_move))
    return false;

  reaching_defs = get_reaching_vdefs (target_loc, is_after, region);

  while (vuses)
    {
      n = VUSE_NUM (vuses);
      for (i = 0; i < n; i++)
        {
          size_t first, last, j, bpos;
          tree vvar;
          tree vop = VUSE_OP (vuses, i);
          vvar = SSA_NAME_VAR (vop);
          bpos = get_vnm_bit_pos (vop, region);
          get_vvar_bit_range (&first, &last, vvar, region);
          for (j = first; j <= last; j++)
            {
              if (TEST_BIT (reaching_defs, j) && (j != bpos))
                return false;
            }
        }
      vuses = vuses->next;
    }
  return true;
}

/* The function returns true if all gimple statements defining
   inner nodes of the expression tree LRS_TREE can be legally
   moved to the target location TARGET_LOC.  IS_AFTER is a flag.
   if it is true, the target location is after TARGET_LOC, 
   otherwise it is before.  */

static bool
ok_to_sched_down (lrs_tree_p lrs_tree, gimple target_loc,
                  bool is_after, lrs_region_p region)
{
  int i = 0;
  int n = VEC_length (gimple, lrs_tree->tree_nodes);

  for (i = 0; i < n; i++)
    {
      gimple to_move = VEC_index (gimple, lrs_tree->tree_nodes, i);
      if (!is_down_motion_legal (target_loc, to_move,
                                 is_after, region))
        return false;
    }
  return true;
}

/* The function returns true if it is benefitial to move tree
   SUB_TREE downward.  */

static inline bool
profitable_to_sched_down (lrs_tree_p sub_tree)
{
  return (sub_tree->num_leaves_not_live_across  == 0);
}

/* For an expression tree LRS_TREE_TO_MOVE whose value has
   multiple uses, this function is used to examine if it is 
   profitable (overlapping live range reduction) move it 
   downward to target location TARGET_LOC.  It it is profitable,
   TARGET_LOC is returned, otherwise the function returns NULL. 
   IS_AFTER is a flag. If it is true, the target location is 
   after TARGET_LOC.  */

static gimple
check_down_motion_profitability (gimple target_loc,
                                 lrs_tree_p lrs_tree_to_move,
                                 bool is_after,
                                 lrs_region_p region)
{
  gimple_stmt_iterator gsi;
  sbitmap live_ur_set;
  int i, n;
  bool use_live_across_target = true;

  if (!profitable_to_sched_down (lrs_tree_to_move))
    return NULL;

  if (is_after)
      live_ur_set = get_across_stmt_use_ref_set (target_loc, region);
  else
    {
      gsi = gsi_for_stmt (target_loc);
      gsi_prev (&gsi);
      if (!gsi_end_p (gsi))
        {
          gimple pstmt = gsi_stmt (gsi);
          live_ur_set = get_across_stmt_use_ref_set (pstmt, region);
        }
      else
        {
          basic_block bb;
          int rid = 0;
          bb = gimple_bb (target_loc);
          get_bb_index_in_region (bb, region, &rid);
          live_ur_set = get_bb_use_ref_in_set (rid, region);
        }
    }

  n = VEC_length (tree, lrs_tree_to_move->leaf_nodes);
  if (n == 0)
    return target_loc;

  for (i = 0; i < n; i++)
    {
      size_t first, last;
      tree use = VEC_index (tree, lrs_tree_to_move->leaf_nodes, i);
      get_def_bit_range (&first, &last, use, region);
      if (sbitmap_range_empty_p (live_ur_set, first, last - first + 1))
        {
          use_live_across_target = false;
          break;
        }
    }

  if (use_live_across_target)
    return target_loc;

  return NULL;
}

static lrs_tree_p
find_lrs_tree (gimple, lrs_region_p);

/* The function performs downward code motion on expression
   tree whose value have multiple uses.  The root of the tree
   is the gimple statement pointed to by the iteration
   GSI_CM_STMT.  */

static gimple_stmt_iterator
sink_multi_use_def (gimple_stmt_iterator gsi_cm_stmt,
                    lrs_region_p region)
{
  gimple cm_stmt, latest;
  gimple_stmt_iterator gsi_prev_stmt;
  gimple_stmt_iterator gsi_target;
  lrs_tree_p cm_stmt_lrs_tree;
  int j, k;
  bool insert_after = false;
  size_t target_order;
  sbitmap reaching_defs;

  cm_stmt = gsi_stmt (gsi_cm_stmt);
  gsi_prev_stmt = gsi_cm_stmt;
  gsi_prev (&gsi_prev_stmt);

  cm_stmt_lrs_tree = find_lrs_tree (cm_stmt, region);
  if (!cm_stmt_lrs_tree)
    return gsi_prev_stmt;

  /* Now adjust the previous statement to be the first
     of the statement group associated with CM_STMT_LRS_TREE  */
  gsi_prev_stmt 
      = gsi_for_stmt (VEC_index (gimple, cm_stmt_lrs_tree->tree_nodes, 0));
  gsi_prev (&gsi_prev_stmt);

  if (has_single_use (gimple_assign_lhs (cm_stmt)))
    return gsi_prev_stmt;

  if (has_float_typed_const_operand (cm_stmt))
    return gsi_prev_stmt;

  latest = get_closest_use (cm_stmt);

  if (!latest)
    return gsi_prev_stmt;

  insert_after = false;
  latest = check_down_motion_target_loc (latest, cm_stmt, 
                                         &insert_after, region);

  if (!latest || latest == cm_stmt)
    return gsi_prev_stmt;

  latest = check_down_motion_profitability (latest, cm_stmt_lrs_tree,
                                            insert_after, region);

  if (latest == NULL)
    return gsi_prev_stmt;

  if (!ok_to_sched_down (cm_stmt_lrs_tree, latest, insert_after, region))
    return gsi_prev_stmt;

  if (!dbg_cnt (lrs))
    return gsi_prev_stmt;

  gsi_target = gsi_for_stmt (latest);
  target_order = get_stmt_order (latest);
  reaching_defs
      = (region->stmt_rd_sets
         ? get_reaching_vdefs (latest, insert_after, region)
         : NULL);
  k = VEC_length (gimple, cm_stmt_lrs_tree->tree_nodes);
  for (j = 0; j < k; j++)
    {
      gimple_stmt_iterator gsi_cm;
      gimple inner_node
          = VEC_index (gimple, cm_stmt_lrs_tree->tree_nodes, j);
      int stmt_id;

      gsi_cm = gsi_for_stmt (inner_node);
      stmt_id = get_stmt_idx_in_region (inner_node);
      if (insert_after)
        {
          gsi_move_after (&gsi_cm, &gsi_target);
          gsi_target = gsi_for_stmt (inner_node);
        }
      else
        gsi_move_before (&gsi_cm, &gsi_target);
      reset_stmt_order (inner_node, target_order);
      if (reaching_defs)
        sbitmap_copy (region->stmt_rd_sets[stmt_id], reaching_defs);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "MOVED (multiuse) DOWN\n");
      print_lrs_tree (dump_file, cm_stmt_lrs_tree);
      fprintf (dump_file, "just %s \n", insert_after? "after" : "before");
      print_gimple_stmt (dump_file, latest, 0, 0);
      fprintf (dump_file, "\n");
    }

  return gsi_prev_stmt;
}

/* The function expands and returns the expression tree rooted
   at statement ROOT.  */

static lrs_tree_p
create_lrs_tree (gimple root, lrs_region_p region)
{
  lrs_tree_p lrs_tree;
  void **slot;

  lrs_tree = (lrs_tree_p) pool_alloc (region->lrs_tree_pool);
  lrs_tree->root = root;
  lrs_tree->tree_nodes = NULL;
  lrs_tree->leaf_nodes = NULL;
  lrs_tree->num_leaves_not_live_across = 0;
  lrs_tree->num_leaves_live_across = 0;
  lrs_tree->num_temp_lrs = 0;

  slot = pointer_map_insert (region->gimple_to_lrs_tree_map, root);
  *slot = lrs_tree;

  return lrs_tree;
}

/* The function returns the lrs_tree created for gimple statement
   STMT which is the tree root.  */

static lrs_tree_p
find_lrs_tree (gimple stmt, lrs_region_p region)
{
  void **slot;

  slot = pointer_map_contains (region->gimple_to_lrs_tree_map, stmt);
  if (!slot)
    return NULL;

  return (lrs_tree_p)*slot;
}

/* The function computes the number of leaf nodes in LRS_TREE that are
   live across (i.e., no references to the same ssa name after ROOT) 
   statement ROOT.  */

static void
check_leaf_liveness (gimple root, lrs_tree_p lrs_tree,
                     lrs_region_p region)
{
  sbitmap live_ur_set;
  int i, n;

  live_ur_set = get_across_stmt_use_ref_set (root, region);

  n = VEC_length (tree, lrs_tree->leaf_nodes);

  for (i = 0; i < n; i++)
    {
      size_t first, last;
      tree leaf = VEC_index (tree, lrs_tree->leaf_nodes, i);
      get_def_bit_range (&first, &last, leaf, region);
      if (sbitmap_range_empty_p (live_ur_set, first, last - first + 1))
        lrs_tree->num_leaves_not_live_across++;
    }

  lrs_tree->num_leaves_live_across = n - lrs_tree->num_leaves_not_live_across;
}

/* The function returns true if STMT is a candidate to be scheduled
   down to basic block SCHED_BB in REGION.  */

static bool
is_down_sched_candidate (gimple stmt, basic_block sched_bb, 
                         lrs_region_p region)
{
  basic_block bb;
  if (!is_gimple_assign (stmt) )
    return false;

  if (!ZERO_SSA_OPERANDS (stmt, SSA_OP_VIRTUAL_DEFS))
    return false;

  if (TREE_CODE (gimple_assign_lhs (stmt)) != SSA_NAME)
    return false;

  bb = gimple_bb (stmt);

  /* can not do code motion across regions.  */
  if (bb->loop_father != sched_bb->loop_father)
    return false;

  if (region->num_bbs == 1 && bb != region->entry)
    return false;

  return true;
}

/* The downward code motion of a statement will shrink the life
   range for the LR that is defined by it, but it may also extend
   the life range of the used LRs if they do not live across the
   insertion point.  If the used LR DO live across the insertion
   point, it will be beneficial to do the code motion.  If they do
   not, this function will try to adjust the insertion point to
   the one they last live.

   Example:


   x = y + z; // statement to be moved

   ....

   a = b + c;

   // insertion point, y, and z live across this point

   t = x + r;

   u = y + 1;

   v = z + 1;

   Since y and z live across the insertion point, it is good to
   to do the code motion and shrink x's range without penalty.


   a = b + c;

   x = y + z; // statement  this is moved

   t = x + r;

   u = y + 1;

   v = z + 1;
*/

static lrs_tree_p
schedule_lrs_tree (gimple root, basic_block sched_bb, lrs_region_p region)
{
  lrs_tree_p lrs_tree = NULL;
  int i, n, num_leaves, nsub;
  lrs_tree_p subtrees[2];
  struct pointer_set_t *leaves;

  if (!is_down_sched_candidate (root, sched_bb, region))
    return NULL;

  lrs_tree = find_lrs_tree (root, region);

  /* Already scheduled  */
  if (lrs_tree)
    return lrs_tree;

  if (!dbg_cnt (lrs))
    return NULL;

  nsub = 0;
  num_leaves = 0;
  lrs_tree = create_lrs_tree (root, region);
  leaves = pointer_set_create ();

  n = gimple_num_ops (root);
  gcc_assert (n < 4);
  for (i = 1; i < n; i++)
    {
      gimple def_stmt;
      lrs_tree_p sub_tree;
      tree op = gimple_op (root, i);
      if (TREE_CODE (op) != SSA_NAME)
        continue;

      def_stmt = SSA_NAME_DEF_STMT (op);
      sub_tree = schedule_lrs_tree (def_stmt, sched_bb, region);
      if (!sub_tree || !has_single_use (op)
          || !ok_to_sched_down (sub_tree, root, false, region)
          || !profitable_to_sched_down (sub_tree))
        {
          if (!pointer_set_insert (leaves, op))
            VEC_safe_push (tree, heap, lrs_tree->leaf_nodes, op);
        }
      else
        {
          int j, k;
          subtrees[nsub++] = sub_tree;
          k = VEC_length (tree, sub_tree->leaf_nodes);
          /* copy leaf nodes  */
          for (j = 0; j < k; j++)
            {
              tree lv = VEC_index (tree, sub_tree->leaf_nodes, j);
              if (!pointer_set_insert (leaves, lv))
                VEC_safe_push (tree, heap, lrs_tree->leaf_nodes, lv);
            }
        }
     }

  if (nsub == 0)
    {
      int nu;
      lrs_stmt_p norm_stmt
          = get_normalized_gimple_stmt (root, region);
      nu = norm_stmt->num_uses;
      for (i = 0; i < nu; i++)
        {
          tree u = *(norm_stmt->uses[i]);
          if (!pointer_set_insert (leaves, u))
            VEC_safe_push (tree, heap, lrs_tree->leaf_nodes, u);
        }
    }

  /* Now compute the number of leaves that do not live across ROOT.  */
  check_leaf_liveness (root, lrs_tree, region);

  /* Subtrees that are scheduled now can be moved down closer to
     the root stmt.  */
  if (nsub == 0)
      lrs_tree->num_temp_lrs = 1;
  else
    {
      int i, j, k; 
      gimple_stmt_iterator target_gsi;
      gimple_stmt_iterator gsi;
      size_t target_order;
      sbitmap reaching_vdefs;

      /* To reduce the max number of temp register required, it is
         better to schedule the subtree with larger temp registers first.  */
      if (nsub == 2 
          && subtrees[0]->num_temp_lrs < subtrees[1]->num_temp_lrs)
        {
          lrs_tree_p first = subtrees[1];
          subtrees[1] = subtrees[0];
          subtrees[0] = first;;
        }

      target_gsi = gsi_for_stmt (root);
      target_order = get_stmt_order (root);
      reaching_vdefs
          = (region->stmt_rd_sets
             ? get_reaching_vdefs (root, false, region)
             : NULL);
      for (i = 0; i < nsub; i++)
        {
          lrs_tree_p sub_tree = subtrees[i];
          k = VEC_length (gimple, sub_tree->tree_nodes);
          for (j = 0; j < k; j++)
            {
              int stmt_id;
              gimple inner_node = VEC_index (gimple, sub_tree->tree_nodes, j);

              stmt_id = get_stmt_idx_in_region (inner_node);

              VEC_safe_push (gimple, heap, lrs_tree->tree_nodes, inner_node);
              gsi = gsi_for_stmt (inner_node);
              gsi_move_before (&gsi, &target_gsi);
              reset_stmt_order (inner_node, target_order);
              if (reaching_vdefs)
                sbitmap_copy (region->stmt_rd_sets[stmt_id], reaching_vdefs);
              if (dump_file && (dump_flags & TDF_DETAILS))
                {
                  fprintf (dump_file, "MOVED DOWN\n");
                  print_lrs_tree (dump_file, sub_tree);
                  fprintf (dump_file, "Before\n");
                  print_gimple_stmt (dump_file, root, 0, 0);
                  fprintf (dump_file, "\n");
                }
            }
        }
      lrs_tree->num_temp_lrs = subtrees[0]->num_temp_lrs;
      if (nsub == 2
          && subtrees[0]->num_temp_lrs == subtrees[1]->num_temp_lrs)
        lrs_tree->num_temp_lrs++;
    }

  VEC_safe_push (gimple, heap, lrs_tree->tree_nodes, root);
  pointer_set_destroy (leaves);
  return lrs_tree;
}

/* The function prepares for downward code motion
   transformation in region REGION.  */

static void
initialize_down_motion (lrs_region_p region)
{
  perform_data_flow_rd (region);
  region->gimple_to_lrs_tree_map
      = pointer_map_create ();
  region->lrs_tree_pool
      = create_alloc_pool ("lrs tree pool",
                           sizeof (struct lrs_tree), 50);
}

/* The function performs downward code motion in REGION
   to reduce overlapping live ranges.  */

static void
shrink_lrs_down_motion (lrs_region_p region)
{
  size_t i;

  if (!do_downward_motion ())
    return;

  initialize_down_motion (region);

  for (i = 0; i < region->num_bbs; i++)
    {
      basic_block bb = region->body[i];
      gimple_stmt_iterator gsi = gsi_start_bb (bb);
      while (!gsi_end_p (gsi))
        {
          schedule_lrs_tree (gsi_stmt (gsi), bb, region);
          gsi_next (&gsi);
        }
    }

  /* Now schedule all the lrs trees that have multiple uses.  */
  for (i = 0; i < region->num_bbs; i++)
    {
      basic_block bb = region->body[i];
      gimple_stmt_iterator gsi = gsi_last_bb (bb);
      while (!gsi_end_p (gsi))
        gsi = sink_multi_use_def (gsi, region);
    }

  dump_data_flow_result (region, "After downward motion");
}

/* The function prepares for the lrs shrinking transformation
   for the current function.  */

static void
init_lrs_shrink (void)
{
  basic_block bb;

  /* TODO -- share loop recog with the reassociation phase.  */
  loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
  calculate_dominance_info (CDI_POST_DOMINATORS);
  stmt_order = pointer_map_create ();
  tmp_reg_alloc_pool
      = create_alloc_pool ("congruent class pool",
                           sizeof (struct reg_alloc), 50);
  tmp_reg_alloc_map = pointer_map_create ();
  reg_alloc_map = pointer_map_create ();
  tmp_reg_alloc_map = pointer_map_create ();
  FOR_EACH_BB (bb)
    {
      compute_stmt_order (bb);
      compute_reg_allocs (bb);
    }
  finalize_reg_allocs ();
  reg_pressure_control_min_bb_size
      = PARAM_VALUE (PARAM_REG_PRESSURE_MIN_BB_FACTOR)
      * target_avail_regs;
}

/* The function destroys the reg alloc map.  */

static void
destroy_reg_alloc_map (void)
{
  size_t i;

  for (i = 0; i < num_reg_allocs; i++)
    VEC_free (tree, heap, reg_allocs[i]);

  pointer_map_destroy (reg_alloc_map);
  reg_alloc_map = NULL;

  free (reg_allocs);
  reg_allocs = NULL;
}

/* The function finalizes function for lrs shrinking.  */

static void
fini_lrs_shrink (void)
{
  destroy_reg_alloc_map ();
  pointer_map_destroy (stmt_order);
  free_dominance_info (CDI_POST_DOMINATORS);
  loop_optimizer_finalize ();
}

/* Entry point for doing live range shrink transformation.  */

static void
do_lr_shrink (void)
{
  basic_block bb;
  FOR_EACH_BB (bb)
    {
      lrs_region_p region = form_region (bb);
      if (!region)
        continue;

      perform_data_flow_ur (region);

      if (!has_high_reg_pressure (region)
	  && need_control_reg_pressure (region) != 2)
	{
	  destroy_region (region);
	  continue;
	}

      shrink_lrs_reassociation (region);

      shrink_lrs_up_motion (region);

      shrink_lrs_down_motion (region);

      /* Now fixup negates if needed  */
      negate_opnds ();

      destroy_region (region);
    }
}

/* Gate and execute functions for live range shrinking.  */

static unsigned int
execute_lrs (void)
{
  init_lrs_shrink ();
  do_lr_shrink ();
  fini_lrs_shrink ();
  return 0;
}

static bool
gate_tree_ssa_lrs (void)
{
  return (flag_tree_lr_shrinking
          && (PARAM_VALUE (PARAM_CONTROL_REG_PRESSURE) != 0));
}

/* Print function for lrs_tree.  DUMP_FILE is the FILE pointer,
   LRS_REASSOC_TREE is the tree to be printed.  */

static void
print_lrs_reassoc_tree (FILE *dump_file, lrs_reassoc_tree_p reassoc_tree)
{
  int i, n;
  n = VEC_length (gimple, reassoc_tree->inner_nodes);
  fprintf (dump_file, "LRS_REASSOC_TREE {\n");
  for (i = 0; i < n; i++)
    {
      gimple stmt = VEC_index (gimple, reassoc_tree->inner_nodes, i);
      fprintf (dump_file, "\t");
      print_gimple_stmt (dump_file, stmt, 0, 0);
    }
  fprintf (dump_file,"}\n");
}

/* Print function for lrs_tree.  DUMP_FILE is the FILE pointer,
   LRS_TREE is the tree to be printed.  */

static void
print_lrs_tree (FILE *dump_file, lrs_tree_p lrs_tree)
{
  int i, n;
  n = VEC_length (gimple, lrs_tree->tree_nodes);
  fprintf (dump_file, "LRS_TREE {\n");
  for (i = 0; i < n; i++)
    {
      gimple stmt = VEC_index (gimple, lrs_tree->tree_nodes, i);
      fprintf (dump_file, "\t");
      print_gimple_stmt (dump_file, stmt, 0, 0);
    }
  fprintf (dump_file,"}\n");
}

/* The function dumps the ssa names referenced in REGION.  The output
   is dumped to DUMP_FILE.  */

static void
dump_refed_names (FILE *dump_file, lrs_region_p region)
{

  size_t i;
  bool is_first = true;
  fprintf (dump_file, "[Refed names]\n\t{ ");
  for (i = 0; i < VEC_length (tree, region->refed_names); i++)
    {
      tree nm;
      if (!is_first)
        fprintf (dump_file, ", ");
      else
        is_first = false;
      nm = VEC_index (tree, region->refed_names, i);
      print_generic_expr (dump_file, nm, 0); 
      fprintf (dump_file, "(%d)", get_reg_alloc_id (nm));
    }
  fprintf (dump_file, "}\n");
}

/* The function dumps the virtual variables referenced in REGION.  The output
   is dumped to DUMP_FILE.  */

static void
dump_refed_vvars (FILE *dump_file, lrs_region_p region)
{
  size_t i;
  bool is_first = true;
  fprintf (dump_file, "[Refed vvar names]\n\t{ ");
  for (i = 0; i < VEC_length (tree, region->refed_vvar_names); i++)
    {
      tree nm;
      if (!is_first)
        fprintf (dump_file, ", ");
      else
        is_first = false;
      nm = VEC_index (tree, region->refed_vvar_names, i);
      print_generic_expr (dump_file, nm, 0); 
    }
  fprintf (dump_file, "}\n");

  is_first = true;
  fprintf (dump_file, "[Refed vvars]\n\t{ ");
  for (i = 0; i < VEC_length (tree, region->refed_vvars); i++)
    {
      tree vvar;
      if (!is_first)
        fprintf (dump_file, ", ");
      else
        is_first = false;
      vvar = VEC_index (tree, region->refed_vvars, i);
      print_generic_expr (dump_file, vvar, 0); 
    }
  fprintf (dump_file, "}\n");
}

/* The function dumps the content of the bitvector BITVEC.  MAPPING is the
   mapping from bit position to ssa name.  Output is dumped to FILE.  */

static void
dump_use_ref_set (FILE *file, sbitmap bitvec, tree *mapping)
{
  unsigned i = 0;
  sbitmap_iterator bi;
  bool first = true;

  fprintf (file, "{");
  EXECUTE_IF_SET_IN_SBITMAP (bitvec, 0, i, bi)
    {
      tree nm = mapping[i];
      if (!first)
        fprintf (file, ", ");
      else
        first = false;

      print_generic_expr (file, nm, 0);
      fprintf (file, "(%d)", i);
    }

  fprintf (file, "}");
}

/* The function computes and dumps register pressure associated with
   use-ref bit vector BITVEC in REGION.  FILE is the output file.  */

static void
dump_register_pressure (FILE *file, sbitmap bitvec,
                        lrs_region_p region)
{
  unsigned gr_pressure = 0;
  unsigned fr_pressure = 0;

  get_num_live_lrs (bitvec, region, &gr_pressure, &fr_pressure);

  fprintf (file, " \n\t[REG PRESSURE: gr = %u, fr = %u]", 
           gr_pressure, fr_pressure);
}

/* The function dumps the use-ref data flow analysis result for 
   basic block BB in REGION.  BB_RIDX is the basis block index in
   REGION, MAPPING is the mapping from bitvector position to ssa names,
   and FILE is the output file.  */

static void
dump_data_flow_bb (FILE *file, basic_block bb, int bb_ridx, 
                   tree *mapping, lrs_region_p region)
{
  gimple_stmt_iterator gsi;

  fprintf (file, "BB#  %d:\n", bb->index);
  fprintf (file, "\tIN :");
  dump_use_ref_set (file, region->bb_use_ref_in_sets[bb_ridx],
                    mapping);
  fprintf (file, "\n");
  fprintf (file, "\tOUT:");
  dump_use_ref_set (file, region->bb_use_ref_out_sets[bb_ridx],
                    mapping);
  fprintf (file, "\n");
  fprintf (file, "\tGEN:");
  dump_use_ref_set (file, region->bb_use_ref_gen_sets[bb_ridx],
                    mapping);
  fprintf (file, "\n");
  fprintf (file, "\tKILL:");
  dump_use_ref_set (file, region->bb_use_ref_kill_sets[bb_ridx],
                    mapping);
  fprintf (file, "\n");

  fprintf (file, "\tREG PRESSURE: gr = %u, fr = %u\n",
           region->bb_reg_pressures[lrc_gr][bb_ridx],
           region->bb_reg_pressures[lrc_fr][bb_ridx]);

  for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      int id;
      gimple stmt = gsi_stmt (gsi);

      id = get_stmt_idx_in_region (stmt);
      fprintf (file, "\t[PHI]: ");
      print_gimple_stmt (file, stmt, 0, 0);
      fprintf (file, "\t\t");
      dump_use_ref_set (file, region->across_stmt_use_ref_sets[id],
                        mapping);
      dump_register_pressure (file, region->across_stmt_use_ref_sets[id],
                              region);
      fprintf (file, "\n");
    }
  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      int id;
      gimple stmt = gsi_stmt (gsi);

      id = get_stmt_idx_in_region (stmt);
      fprintf (file, "\t[STMT]: ");
      print_gimple_stmt (file, stmt, 0, 0);
      fprintf (file, "\t\t");
      dump_use_ref_set (file, region->across_stmt_use_ref_sets[id],
                        mapping);
      dump_register_pressure (file, region->across_stmt_use_ref_sets[id],
                              region);
      fprintf (file, "\n");
    }
}

/* The function dumps the use-ref data flow result for REGION.  PHASE is 
   the string of the dump phase.  */

static void
dump_data_flow_result (lrs_region_p region, const char* phase)
{
  size_t i, n;
  tree *bit_pos_to_tree_mapping = 0;

  if (!dump_file)
    return;

  fprintf (dump_file, "[Data Flow Result for region (head bb): %d:  PHASE: %s\n\n",
           region->entry->index, phase);

  dump_reg_allocs (dump_file);

  dump_refed_names (dump_file, region);
  dump_refed_vvars (dump_file, region);

  fprintf (dump_file, "\tREG PRESSURE: gr = %u, fr = %u\n",
           region->reg_pressure[lrc_gr],
           region->reg_pressure[lrc_fr]);

  fprintf (dump_file, "\tAVAIL REGS: gr = %u, fr = %u\n",
           region->available_regs[lrc_gr],
           region->available_regs[lrc_fr]);

  bit_pos_to_tree_mapping = XNEWVEC (tree, region->bitvec_width);
  n = VEC_length (tree, region->refed_names);
  for (i = 0; i < n; i++)
    {
      size_t first, last, j;
      tree nm = VEC_index (tree, region->refed_names, i);
      get_def_bit_range (&first, &last, nm, region);
      for (j = first; j <= last; j++)
        bit_pos_to_tree_mapping[j] = nm;
    }

  for (i = 0; i < region->num_bbs; i++)
    dump_data_flow_bb (dump_file, region->body[i], i,
                       bit_pos_to_tree_mapping, region);

  free (bit_pos_to_tree_mapping);
}

/* The functions dumps the reaching def bitvector
   BITVEC.  REFED_VNAMES is a map from bit positions
   to the virtual variable names.  */

static void
dump_rd_set (FILE *file, sbitmap bitvec, 
             VEC(tree, heap) *refed_vnames)
{
  unsigned i = 0;
  sbitmap_iterator bi;
  bool first = true;

  fprintf (file, "{");
  EXECUTE_IF_SET_IN_SBITMAP (bitvec, 0, i, bi)
    {
      tree nm = VEC_index (tree, refed_vnames, i);
      if (!first)
        fprintf (file, ", ");
      else
        first = false;

      print_generic_expr (file, nm, 0);
      fprintf (file, "(%d)", i);
    }

  fprintf (file, "}");
}

/* The function dumps virtual variable reaching def data flow
   results for basic block BB (with id BB_RIDX) in REGION.  */

static void
dump_data_flow_bb_rd (FILE *file, basic_block bb, int bb_ridx, 
                      lrs_region_p region)
{
  gimple_stmt_iterator gsi;
  VEC(tree, heap) *refed_vnames = region->refed_vvar_names;

  fprintf (file, "BB#  %d:\n", bb->index);
  fprintf (file, "\tIN :");
  dump_rd_set (file, region->bb_rd_in_sets[bb_ridx], refed_vnames);
  fprintf (file, "\n");
  fprintf (file, "\tOUT:");
  dump_rd_set (file, region->bb_rd_out_sets[bb_ridx], refed_vnames);
  fprintf (file, "\n");
  fprintf (file, "\tGEN:");
  dump_rd_set (file, region->bb_rd_gen_sets[bb_ridx], refed_vnames);
  fprintf (file, "\n");
  fprintf (file, "\tKILL:");
  dump_rd_set (file, region->bb_rd_kill_sets[bb_ridx], refed_vnames);
  fprintf (file, "\n");

  for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      int id;
      gimple stmt = gsi_stmt (gsi);

      id = get_stmt_idx_in_region (stmt);
      fprintf (file, "\t[PHI]: ");
      print_gimple_stmt (file, stmt, 0, 0);
      fprintf (file, "\t\t");
      dump_rd_set (file, region->stmt_rd_sets[id], refed_vnames);
      fprintf (file, "\n");
    }
  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      int id;
      gimple stmt = gsi_stmt (gsi);

      id = get_stmt_idx_in_region (stmt);
      fprintf (file, "\t[STMT]: ");
      print_gimple_stmt (file, stmt, 0, 0);
      fprintf (file, "\t\t");
      dump_rd_set (file, region->stmt_rd_sets[id], refed_vnames);
      fprintf (file, "\n");
    }
}

/* The function dumps virtual variable reaching def data
   flow result for region REGION.  */

static void
dump_data_flow_result_rd (lrs_region_p region)
{
  size_t i;

  if (!dump_file)
    return;

  fprintf (dump_file, "[Data Flow Result (Reach Def) for region (head bb): %d\n\n",
           region->entry->index);

  dump_refed_vvars (dump_file, region);

  for (i = 0; i < region->num_bbs; i++)
    dump_data_flow_bb_rd (dump_file, region->body[i], i, region);

}

/* The function dumps one reg alloc RA.  */
static bool
dump_ra (FILE *file, VEC(tree, heap) *ra)
{
  size_t i;

  fprintf (file, "\t{ ");
  for (i = 0; i < VEC_length (tree, ra); i++)
    {
      tree nm = VEC_index (tree, ra, i);
      print_generic_expr (file, nm, 0);
      fprintf (file, " ");
    }
  fprintf (file, "}\n");
  return true;
}

/* The function dumps reg allocs computed.  */

static void
dump_reg_allocs (FILE *file)
{
  size_t i;
  fprintf (file, "[Reg Alloc Congruent Classes]\n");

  for (i = 0; i < num_reg_allocs; i++)
    dump_ra (file, reg_allocs[i]);
}

struct gimple_opt_pass pass_lrs =
{
 {
  GIMPLE_PASS,
  "lrs",				/* name */
  gate_tree_ssa_lrs,     		/* gate */
  execute_lrs,		         	/* execute */
  NULL,					/* sub */
  NULL,					/* next */
  0,					/* static_pass_number */
  TV_TREE_LRS,	         		/* tv_id */
  PROP_cfg | PROP_ssa | PROP_alias,	/* properties_required */
  0,					/* properties_provided */
  0,					/* properties_destroyed */
  0,					/* todo_flags_start */
  TODO_dump_func | TODO_ggc_collect | TODO_verify_ssa /* todo_flags_finish */
 }
};
