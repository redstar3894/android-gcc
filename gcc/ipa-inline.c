/* Inlining decision heuristics.
   Copyright (C) 2003, 2004, 2007, 2008, 2009 Free Software Foundation, Inc.
   Contributed by Jan Hubicka

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

/*  Inlining decision heuristics

    We separate inlining decisions from the inliner itself and store it
    inside callgraph as so called inline plan.  Refer to cgraph.c
    documentation about particular representation of inline plans in the
    callgraph.

    There are three major parts of this file:

    cgraph_mark_inline implementation

      This function allows to mark given call inline and performs necessary
      modifications of cgraph (production of the clones and updating overall
      statistics)

    inlining heuristics limits

      These functions allow to check that particular inlining is allowed
      by the limits specified by user (allowed function growth, overall unit
      growth and so on).

    inlining heuristics

      This is implementation of IPA pass aiming to get as much of benefit
      from inlining obeying the limits checked above.

      The implementation of particular heuristics is separated from
      the rest of code to make it easier to replace it with more complicated
      implementation in the future.  The rest of inlining code acts as a
      library aimed to modify the callgraph and verify that the parameters
      on code size growth fits.

      To mark given call inline, use cgraph_mark_inline function, the
      verification is performed by cgraph_default_inline_p and
      cgraph_check_inline_constraints.

      The heuristics implements simple knapsack style algorithm ordering
      all functions by their "profitability" (estimated by code size growth)
      and inlining them in priority order.

      cgraph_decide_inlining implements heuristics taking whole callgraph
      into account, while cgraph_decide_inlining_incrementally considers
      only one function at a time and is used by early inliner.

   The inliner itself is split into several passes:

   pass_inline_parameters

     This pass computes local properties of functions that are used by inliner:
     estimated function body size, whether function is inlinable at all and
     stack frame consumption.

     Before executing any of inliner passes, this local pass has to be applied
     to each function in the callgraph (ie run as subpass of some earlier
     IPA pass).  The results are made out of date by any optimization applied
     on the function body.

   pass_early_inlining

     Simple local inlining pass inlining callees into current function.  This
     pass makes no global whole compilation unit analysis and this when allowed
     to do inlining expanding code size it might result in unbounded growth of
     whole unit.

     The pass is run during conversion into SSA form.  Only functions already
     converted into SSA form are inlined, so the conversion must happen in
     topological order on the callgraph (that is maintained by pass manager).
     The functions after inlining are early optimized so the early inliner sees
     unoptimized function itself, but all considered callees are already
     optimized allowing it to unfold abstraction penalty on C++ effectively and
     cheaply.

   pass_ipa_early_inlining

     With profiling, the early inlining is also necessary to reduce
     instrumentation costs on program with high abstraction penalty (doing
     many redundant calls).  This can't happen in parallel with early
     optimization and profile instrumentation, because we would end up
     re-instrumenting already instrumented function bodies we brought in via
     inlining.

     To avoid this, this pass is executed as IPA pass before profiling.  It is
     simple wrapper to pass_early_inlining and ensures first inlining.

   pass_ipa_inline

     This is the main pass implementing simple greedy algorithm to do inlining
     of small functions that results in overall growth of compilation unit and
     inlining of functions called once.  The pass compute just so called inline
     plan (representation of inlining to be done in callgraph) and unlike early
     inlining it is not performing the inlining itself.

   pass_apply_inline

     This pass performs actual inlining according to pass_ipa_inline on given
     function.  Possible the function body before inlining is saved when it is
     needed for further inlining later.
 */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "tree.h"
#include "tree-inline.h"
#include "langhooks.h"
#include "flags.h"
#include "cgraph.h"
#include "diagnostic.h"
#include "toplev.h"
#include "timevar.h"
#include "params.h"
#include "fibheap.h"
#include "intl.h"
#include "tree-pass.h"
#include "hashtab.h"
#include "coverage.h"
#include "ggc.h"
#include "tree-flow.h"
#include "rtl.h"
#include "ipa-prop.h"
#include "basic-block.h"
#include "tree-sample-profile.h"
#include "toplev.h"
#include "dbgcnt.h"
#include "tree-dump.h"

#include <math.h>

/* Mode incremental inliner operate on:

   In ALWAYS_INLINE only functions marked
   always_inline are inlined.  This mode is used after detecting cycle during
   flattening.

   In SIZE mode, only functions that reduce function body size after inlining
   are inlined, this is used during early inlining.

   in ALL mode, everything is inlined.  This is used during flattening.  */
enum inlining_mode {
  INLINE_NONE = 0,
  INLINE_ALWAYS_INLINE,
  INLINE_SIZE,
  INLINE_ALL
};

/* List of user-specified plans for inlining passes.  Specified with
   -finline-plan-<pass>=<file>.  */

struct inline_plan_file *inline_plan_files;

/* A linked list of callsites used to describe a chain of inlined
   callsites which describes the context of an inlining decision.  The
   first element in the list is the outermost containing function.
   The last two elements are the caller and callee of the inlined
   edge.  */
const char *inlining_mode_strings[] = { "INLINE_NONE",
					"INLINE_ALWAYS_INLINE",
					"INLINE_SIZE",
					"INLINE_ALL" };

struct callsite_chain {
  char *function_name;
  int callsite_no;
  struct callsite_chain *next;
};

/* Defines a specific inlining decision in an inline plan file.  */

struct inline_decision {
  struct callsite_chain *chain;
  int line_no;
  struct inline_decision *next;
};

/* Defines the set of decisions in an inline plan file.  */

struct inline_plan {
  struct inline_plan_file *file;
  struct inline_decision *decisions;
};

/* If non-NULL, then the plan for the current early inlining pass.  */

struct inline_plan *einline_plan;

static bool
cgraph_decide_inlining_incrementally (struct cgraph_node *, enum inlining_mode,
				      int);


/* Statistics we collect about inlining algorithm.  */
static int ncalls_inlined;
static int nfunctions_inlined;
static int overall_insns;
static gcov_type max_count;

/* Holders of ipa cgraph hooks: */
static struct cgraph_node_hook_list *function_insertion_hook_holder;

/* Return the stringified value of enum function_frequency for
   NODE.  */

static const char *
function_frequency_string (const struct cgraph_node *node)
{
  struct function *fun = DECL_STRUCT_FUNCTION (node->decl);
  const char *freq_str = "FREQUENCY_UNKNOWN";
  if (fun)
    {
      switch (fun->function_frequency)
	{
	case (FUNCTION_FREQUENCY_UNLIKELY_EXECUTED):
	  freq_str = "FUNCTION_FREQUENCY_UNLIKELY_EXECUTED";
	  break;
	case (FUNCTION_FREQUENCY_NORMAL):
	  freq_str = "FUNCTION_FREQUENCY_NORMAL";
	  break;
	case (FUNCTION_FREQUENCY_HOT):
	  freq_str = "FUNCTION_FREQUENCY_HOT";
	  break;
	}
    }
  return freq_str;
}

/* Data structures for hot components.  */
struct hot_component {
  struct cgraph_node *root;
  int uid;
  int size;
  int original_size;
};

struct hot_component_list
{
  struct hot_component *component;
  struct hot_component_list *next;
};

/* Total number of hot components.  */
static int n_hot_components = 0;
/* Array containing all hot components.  Indexed by component uid.  */
static struct hot_component *hot_components = NULL;
/* Lists of hot components of each cgraph node.  Indexed by node uid.  */
static struct hot_component_list **node_hot_component_list = NULL;
/* Size of NODE_HOT_COMPONENT_LIST.  */
static int hot_component_max_id = 0;


static inline struct inline_summary *
inline_summary (struct cgraph_node *node)
{
  return &node->local.inline_summary;
}

/* Return the pointer to the list of hot components for NODE.  Global
   array NODE_HOT_COMPONENT_LIST is resized as necessary for new nodes
   with uid's that exceed the bounds of the current array.  This may
   occur due to cloning.  */

static struct hot_component_list**
hot_component_list_for_node (struct cgraph_node *node)
{
  if (node->uid >= hot_component_max_id)
    {
      int i, newsize;

      newsize = node->uid * 2;
      node_hot_component_list =
        XRESIZEVEC (struct hot_component_list *, node_hot_component_list,
                    newsize);
      for (i = hot_component_max_id; i < newsize; i++)
        node_hot_component_list[i] = NULL;
      hot_component_max_id = newsize;
    }
  return &node_hot_component_list[node->uid];
}

/* Return true if NODE is in the hot component with uid UID.  */

static bool
node_in_hot_component_p (struct cgraph_node *node, int uid)
{
  struct hot_component_list *p;

  for (p = *(hot_component_list_for_node (node)); p; p = p->next)
    if (p->component->uid == uid)
      return true;
  return false;
}

/* Performs a downward DFS search from NODE in the hot call graph, and
   marks all successors of NODE by setting its respective bit in
   SUCCESSORS.  */

static void
mark_all_successors  (struct cgraph_node *node, sbitmap successors)
{
  struct cgraph_edge *edge;

  SET_BIT (successors, node->uid);
  for (edge = node->callees; edge; edge = edge->next_callee)
    if (cgraph_maybe_hot_edge_p (edge)
        && !TEST_BIT (successors, edge->callee->uid))
      mark_all_successors (edge->callee, successors);
}

/* Performs an upward DFS search from NODE in the hot call graph.  If
   a node is encountered whose bit is not set in sbitmap MARKED, then
   return false otherwise return true.  As each node is visited, the
   node's corresponding element in VISITED is set to ID.  */

static bool
has_unmarked_predecessor_p  (struct cgraph_node *node, sbitmap marked,
                             int *visited, int id)
{
  struct cgraph_edge *edge;

  visited[node->uid] = id;
  for (edge = node->callers; edge; edge = edge->next_caller)
    if (cgraph_maybe_hot_edge_p (edge)
        && visited[edge->caller->uid] != id)
      {
        if (!TEST_BIT (marked, edge->caller->uid))
          /* An unmarked predecessor was encountered.  */
          return true;
        /* Continue upward DFS search.  */
        if (has_unmarked_predecessor_p (edge->caller, marked,
                                        visited, id))
            return true;
      }
  return false;
}

/* Add NODE to hot component COMP.  */

static void
add_node_to_hot_component (struct hot_component *comp,
                           struct cgraph_node *node)
{
  struct hot_component_list *p = XNEW (struct hot_component_list);
  p->component = comp;
  p->next = *(hot_component_list_for_node (node));
  *(hot_component_list_for_node (node)) = p;
}

/* Perform a downward DFS seach in the hot call graph, and mark NODE
   as a member of hot component COMP.  Returns the total number of hot
   insns beneath this point in the DFS search.  As each node is
   visited, set the corresponding element in VISITED to ID.  */

static int
construct_hot_component (struct cgraph_node *node, struct hot_component *comp,
                         int *visited, int id)
{
  struct cgraph_edge *edge;
  int size = node->local.inline_summary.self_hot_insns;

  visited[node->uid] = id;
  add_node_to_hot_component (comp, node);
  for (edge = node->callees; edge; edge = edge->next_callee)
    if (cgraph_maybe_hot_edge_p (edge)
        && visited[edge->callee->uid] != id)
      size += construct_hot_component (edge->callee, comp, visited, id);
  return size;
}

/* Recompute the hot components which NODE is contained in.  */

static void
update_hot_components_for_node (struct cgraph_node *node)
{
  struct cgraph_edge *e;
  struct hot_component_list *p, *tmp;

  /* Free old list.  */
  p = *(hot_component_list_for_node (node));
  while (p)
    {
      tmp = p->next;
      free (p);
      p = tmp;
    }
  *(hot_component_list_for_node (node)) = NULL;

  /* Hot components of NODE is the union of all hot components of
     NODE's hot callers.  */
  for (e = node->callers; e; e = e->next_caller)
    if (cgraph_maybe_hot_edge_p (e))
      for (p = *(hot_component_list_for_node (e->caller)); p; p = p->next)
        if (!node_in_hot_component_p (node, p->component->uid))
          add_node_to_hot_component (p->component, node);
}

/* Identify the hot components of the call graph, and construct data
   structures to track their size and growth.

   A hot component is a connected component of maximum size in the hot
   call graph, where the hot call graph is the subgraph of the call
   graph induced by all hot nodes and hot edges.  The total number of
   hot instructions in the component (its size) is roughly the I-cache
   footprint of this hot region of code.  Limiting the size of the hot
   component can prevent I-cache thrashing.

   Each hot component is defined by a root.  In the simple case, a
   root is a hot function with no incoming hot edges (with any number
   of outgoing hot edges).  In the more complicated case with
   recursion, a root can be a member of strongly connected component
   in the hot call graph which has no incoming hot edges from outside
   the strongly connected component.  In both cases, the hot component
   is defined as the root plus the successors of the root in the hot
   call graph.  Typically the root is a function with an un-hot entry
   that contains a hot loop and all functions called transitively
   along hot edges from within the loop.  */

struct node_list
{
  struct cgraph_node *node;
  struct node_list *next;
};

void
compute_hot_components (void)
{
  struct cgraph_node *node;
  struct node_list *p;
  struct node_list *roots = NULL;
  sbitmap successor;
  int *visited;
  int uid, i;

  /* VISITED is used to flag nodes which have already been visited
     during some DFS searches.  If VISITED[UID] equals some_unique_id,
     then the cgraph node with uid UID has been visited.  This
     mechanism is preferable for some searches to a sbitmap, because
     it not need to be reset between sequential searches which overlap
     in the call graph, only a new unique id needs to be chosen.  */
  visited = XNEWVEC (int, cgraph_max_uid);
  for (i = 0; i < cgraph_max_uid; i++)
    visited[i] = -1;

  /* Identify a root node for each hot component.  A node is a root if
     all of its predecessors (if any) in the hot call graph are also
     successors.  */
  n_hot_components = 0;
  successor = sbitmap_alloc (cgraph_max_uid);
  sbitmap_zero (successor);
  for (node = cgraph_nodes; node; node = node->next)
    if (hot_function_p (node))
      {
        /* If NODE is a successor of a node previously handled in this
           loop, then no need to consider it as a root node.  */
        if (TEST_BIT(successor, node->uid))
          continue;

        /* Set bit in successor of NODE and all successors of NODE.
           An sbitmap is used (rather than the int visited array)
           because "successor" state is preserved across calls to
           mark_all_successors.  State is not cleared.  */
        mark_all_successors (node, successor);

        /* VISITED array is used to mark nodes for upward DFS searches
           because subsequent has_marked_predecessor searches may
           overlap previous searches in the call graph, and we don't
           want to reset a bitmap every time.  ID for visited array is
           call graph node uid.  */
        if (!has_unmarked_predecessor_p (node, successor, visited, node->uid))
          {
            struct node_list *elem = XNEW (struct node_list);
            elem->node = node;
            elem->next = roots;
            roots = elem;
            n_hot_components++;
          }
      }
  sbitmap_free (successor);

  if (n_hot_components)
    {
      /* Allocate global state for hot components.  For
         NODE_HOT_COMPONENT_LIST (indexed by call graph node uid),
         allocate twice the current max node uid to allow for call graph
         node cloning.  Array is dynamically resized in the unlikely event
         this is insufficient.  */
      hot_components = XNEWVEC (struct hot_component, n_hot_components);

      hot_component_max_id = cgraph_max_uid * 2;
      node_hot_component_list = XCNEWVEC (struct hot_component_list *,
                                          hot_component_max_id);

      /* Reset VISITED array.  */
      for (i = 0; i < cgraph_max_uid; i++)
        visited[i] = -1;

      /* Iterate through list of root nodes and construct hot
         components.  */
      uid = 0;
      p = roots;
      while (p)
        {
          struct node_list *tmp;

          hot_components[uid].root = p->node;
          hot_components[uid].uid = uid;
          /* Identify all nodes in the hot component with a downward
             DFS search from the root.  Use VISITED array as
             subsequent searches may overlap (ie, a node may be in
             more than one hot component).  ID for visited array is
             uid of the root node.  */
          hot_components[uid].size =
            construct_hot_component (hot_components[uid].root,
                                     &hot_components[uid],
                                     visited, uid);
          hot_components[uid].original_size = hot_components[uid].size;
          uid++;

          /* Free node_list element.  */
          tmp = p->next;
          free (p);
          p = tmp;
        }
    }
  free (visited);

#ifdef ENABLE_CHECKING
  verify_hot_components ();
#endif
}

/* Perform a downward DFS seach in the hot call graph.  Verifies NODE
   is in hot component with uid UID.  Accumulates total number of hot
   insns in *SIZE.  Returns the number of call graph nodes beneath
   this point in the DFS search.  */

static int
verify_hot_components_1 (struct cgraph_node *node, sbitmap visited,
                         int comp_uid, int *size)
{
  struct cgraph_edge *edge;
  int nnodes = 1;

  SET_BIT (visited, node->uid);
  *size += node->local.inline_summary.self_hot_insns;
  for (edge = node->callees; edge; edge = edge->next_callee)
    if (cgraph_maybe_hot_edge_p (edge)
        && !TEST_BIT (visited, edge->callee->uid))
      {
        gcc_assert (node_in_hot_component_p (edge->callee, comp_uid));
        nnodes += verify_hot_components_1 (edge->callee, visited,
                                           comp_uid, size);
      }
  return nnodes;
}

/* Verify global data structures for hot components.  */

void
verify_hot_components (void)
{
  if (n_hot_components)
    {
      int i;
      struct cgraph_node *node;
      sbitmap visited = sbitmap_alloc (cgraph_max_uid);

      /* Each hot function must be in at least one hot component, and a
         non-hot function must not be in a hot component.  */
      for (node = cgraph_nodes; node; node = node->next)
        {
          struct hot_component_list *lst = *(hot_component_list_for_node (node));
          gcc_assert ((hot_function_p (node) && lst)
                      || (!hot_function_p (node) && !lst));
        }

      /* Verify each hot component.  */
      for (i = 0; i < n_hot_components; i++)
        {
          struct hot_component *comp = &hot_components[i];
          struct hot_component_list *root_lst =
            *(hot_component_list_for_node (comp->root));
          int nnodes;
          int size = 0;

          /* The root node of each hot component must be in exactly
             one hot component (the component it is the root of).  */
          gcc_assert (root_lst && !root_lst->next);
          gcc_assert (node_in_hot_component_p (comp->root, comp->uid));

          /* Every node accessible via downward DFS search in the hot
             call graph from a root node must be in the root node's
             hot component, and these nodes are the only nodes in the
             hot component.  */
          sbitmap_zero (visited);
          nnodes = verify_hot_components_1 (comp->root, visited,
                                            comp->uid, &size);
          gcc_assert (size == comp->size);
          /* Count down nodes which are found to in a dumb search
             through the hot component lists of cgraph nodes.  */
          for (node = cgraph_nodes; node; node = node->next)
            if (hot_function_p (node)
                && node_in_hot_component_p (node, comp->uid))
              nnodes--;
          gcc_assert (nnodes == 0);
        }
      sbitmap_free (visited);
    }
}

/* Free all global data structures for hot components.  */

void
free_hot_components (void)
{
  if (n_hot_components)
    {
      int i;

      n_hot_components = 0;
      free (hot_components);
      hot_components = NULL;
      for (i = 0; i < hot_component_max_id; i++)
        {
          struct hot_component_list *tmp, *p = node_hot_component_list[i];
          while (p)
            {
              tmp = p->next;
              free (p);
              p = tmp;
            }
        }
      hot_component_max_id = 0;
      free (node_hot_component_list);
      node_hot_component_list = NULL;
    }
}

/* Return the growth in insns of the hot component with uid UID if
   EDGE is inlined.  */

static int
hot_component_growth_after_inlining (struct cgraph_edge *edge, int uid)
{
  struct cgraph_edge *e;
  int code_duplication = 0;

  if (!node_in_hot_component_p (edge->callee, uid))
    return 0;

  /* If a hot caller of EDGE's callee (other than EDGE) is also
     contained in this hot component, then the hot component will grow
     by the number of hot insns in the callee.

     In this case, if EDGE is inlined both the old and duplicated node
     will be in the hot component.  */
  for (e = edge->callee->callers; e; e = e->next_caller)
    {
      if (e == edge || !cgraph_maybe_hot_edge_p (e))
        continue;

      if (node_in_hot_component_p (e->caller, uid))
        {
          /* Function body will be duplicated within component.  */
          code_duplication = edge->callee->local.inline_summary.self_hot_insns;
          break;
        }
    }

  return code_duplication;
}

static void
dump_hot_components_1 (FILE *f, struct cgraph_node *node, sbitmap visited,
                       int indent, struct cgraph_edge *incoming_edge)
{
  int i;
  struct hot_component_list *p;

  for (i = 0; i < indent; i++)
    fprintf (f, "  ");
  fprintf (f, "%s/%d", cgraph_node_name (node), node->uid);
  if (incoming_edge && !incoming_edge->inline_failed)
    fprintf (f, " (INLINED)");
  fprintf (f, " insns hot/all %d/%d, in components (",
           node->local.inline_summary.self_hot_insns,
           node->local.inline_summary.self_insns);
  for (p = *(hot_component_list_for_node (node)); p; p = p->next)
    fprintf (f, " %d", p->component->uid);
  fprintf (f, " )");

  if (TEST_BIT (visited, node->uid))
    /* NODE has already been dumped earlier in the output. */
    fprintf (f, " [repeat]\n");
  else
    {
      struct cgraph_edge *edge;

      fprintf (f, "\n");
      SET_BIT (visited, node->uid);
      for (edge = node->callees; edge; edge = edge->next_callee)
        if (cgraph_maybe_hot_edge_p (edge))
          dump_hot_components_1 (f, edge->callee, visited, indent + 1, edge);
    }
}

/* Dump the functions within each hot components to F in a tree
   format. */

void
dump_hot_components (FILE *f)
{
  sbitmap visited = sbitmap_alloc (cgraph_max_uid);
  int i;

  for (i = 0; i < n_hot_components; i++)
    {
      sbitmap_zero (visited);
      fprintf (f, "Hot component %d (hot insns = %d):\n", hot_components[i].uid,
               hot_components[i].size);
      dump_hot_components_1 (f, hot_components[i].root, visited, 1, NULL);
    }
  sbitmap_free (visited);
}

/* Estimate size of the function after inlining WHAT into TO.  */

static int
cgraph_estimate_size_after_inlining (int times, struct cgraph_node *to,
				     struct cgraph_node *what)
{
  int size;
  tree fndecl = what->decl, arg;
  int call_insns = PARAM_VALUE (PARAM_INLINE_CALL_COST);

  for (arg = DECL_ARGUMENTS (fndecl); arg; arg = TREE_CHAIN (arg))
    call_insns += estimate_move_cost (TREE_TYPE (arg));
  size = (what->global.insns - call_insns) * times + to->global.insns;
  gcc_assert (size >= 0);
  return size;
}

/* E is expected to be an edge being inlined.  Clone destination node of
   the edge and redirect it to the new clone.
   DUPLICATE is used for bookkeeping on whether we are actually creating new
   clones or re-using node originally representing out-of-line function call.
   */
void
cgraph_clone_inlined_nodes (struct cgraph_edge *e, bool duplicate,
			    bool update_original)
{
  HOST_WIDE_INT peak;

  if (duplicate)
    {
      /* We may eliminate the need for out-of-line copy to be output.
	 In that case just go ahead and re-use it.  */
      if (!e->callee->callers->next_caller
	  && !e->callee->needed
	  && !cgraph_new_nodes)
	{
	  gcc_assert (!e->callee->global.inlined_to);
	  if (e->callee->analyzed)
	    overall_insns -= e->callee->global.insns, nfunctions_inlined++;
	  duplicate = false;
	}
      else
	{
	  struct cgraph_node *n, *orig_callee = e->callee;
          bool update_hot_components =
            (flag_limit_hot_components && n_hot_components
             && cgraph_maybe_hot_edge_p (e));

	  if (update_hot_components)
            {
              struct hot_component_list *p;

              /* Update component sizes due to inlining edge before
                 cloning because hot_component_growth_after_inlining()
                 requires the edge be in its pre-inlined position.  */
              for (p = *(hot_component_list_for_node (e->caller)); p;
                   p = p->next)
                p->component->size +=
                  hot_component_growth_after_inlining (e, p->component->uid);
            }

          n = cgraph_clone_node (e->callee, e->count, e->frequency,
                                 e->loop_nest, update_original);
	  cgraph_redirect_edge_callee (e, n);

	  if (update_hot_components)
            {
              update_hot_components_for_node (n);
              update_hot_components_for_node (orig_callee);
            }
	}
    }

  if (e->caller->global.inlined_to)
    e->callee->global.inlined_to = e->caller->global.inlined_to;
  else
    e->callee->global.inlined_to = e->caller;
  e->callee->global.stack_frame_offset
    = e->caller->global.stack_frame_offset
      + inline_summary (e->caller)->estimated_self_stack_size;
  peak = e->callee->global.stack_frame_offset
      + inline_summary (e->callee)->estimated_self_stack_size;
  if (e->callee->global.inlined_to->global.estimated_stack_size < peak)
    e->callee->global.inlined_to->global.estimated_stack_size = peak;
  e->callee->global.inlined_to->global.estimated_stack_size_pessimistic +=
      inline_summary (e->callee)->estimated_self_stack_size;

  /* Recursively clone all bodies.  */
  for (e = e->callee->callees; e; e = e->next_callee)
    if (!e->inline_failed)
      cgraph_clone_inlined_nodes (e, duplicate, update_original);
}


/* Allocates and returns a unique name for NODE.  For most nodes this
   is simply the result of cgraph_node_name.  For versioned clones
   which share a common cgraph_node_name, the assembly name is
   appended.  */

static char*
create_unique_cgraph_node_name (struct cgraph_node *node)
{
  char *name;
  int len = strlen (cgraph_node_name (node)) + 1;
  if (node->is_versioned_clone)
    {
      gcc_assert (DECL_ASSEMBLER_NAME_SET_P (node->decl));
      len += strlen (" (clone )");
      len += strlen (IDENTIFIER_POINTER (decl_assembler_name (node->decl)));
    }
  name = XNEWVEC (char, len);
  if (node->is_versioned_clone)
    sprintf (name, "%s (clone %s)", cgraph_node_name (node),
             IDENTIFIER_POINTER (decl_assembler_name (node->decl)));
  else
    strcpy (name, cgraph_node_name (node));
  return name;
}

/* Print a unique name for NODE to F.  This is the same name as
   create_unique_cgraph_node_name, but this function doesn't allocate
   memory.  */

static void
dump_unique_cgraph_node_name (FILE *f, struct cgraph_node *node)
{
  fprintf (f, cgraph_node_name (node));
  if (node->is_versioned_clone)
    {
      gcc_assert (DECL_ASSEMBLER_NAME_SET_P (node->decl));
      fprintf (f, " (clone %s)",
               IDENTIFIER_POINTER (decl_assembler_name (node->decl)));
    }
}

/* Returns true if the unique name of NODE is NAME.  */

static bool
cgraph_node_matches_unique_name_p (struct cgraph_node *node, const char *name)
{
  char *node_name = create_unique_cgraph_node_name (node);
  bool matches = (strcmp (node_name, name) == 0);
  free (node_name);
  return matches;
}

/* Return the ordinal position of the callsite of EDGE among all calls
   of EDGE->CALLEE in EDGE->CALLER.  Numbering starts at 1, so the
   edge of the first call returns 1, the second returns 2, etc.  */

static int
callsite_position (struct cgraph_edge *edge)
{
  int c = 1;
  struct cgraph_edge *e;

  /* The list of call graph edges are in the inverse order in which
     their respective callsites appear in the function, so count the
     number of edges after EDGE with the same callee.  */
  for (e = edge->next_callee; e; e = e->next_callee)
    if (e->callee->decl == edge->callee->decl)
      c++;

  return c;
}

/* For the inlined edge EDGE, dump (into F) the chain of inlined
   callsites from the enclosing function down to EDGE's callee.  For
   example, suppose FuncC calls FuncB calls FuncA.  If FuncA is
   inlined into an inlined copy of FuncB called by FuncC, then the
   chain for this particular edge FuncB->FuncA might look like:

     FuncA @callsite #1 into FuncB @callsite #3 into FuncC

   Simlilar callsites (same caller, same callee) are numbered
   consecutively from the beginning of the caller to uniquely identify
   multiple calls to the same function.

   This chain precisely describes the context of inlining a particular
   edge.  The format of this dump is the same as that used to describe
   inlined callsites in the inline plan specified with
   -finline-plan-<pass>=<file>.  */

static void
dump_inlining_decision (FILE *f, struct cgraph_edge *edge)
{
  dump_unique_cgraph_node_name (f, edge->callee);
  fprintf (f, " @callsite #%d into ", callsite_position (edge));
  if (edge->caller->global.inlined_to)
    dump_inlining_decision (f, edge->caller->callers);
  else
    dump_unique_cgraph_node_name (f, edge->caller);
}

/* Mark edge E as inlined and update callgraph accordingly.  UPDATE_ORIGINAL
   specify whether profile of original function should be updated.  If any new
   indirect edges are discovered in the process, add them to NEW_EDGES, unless
   it is NULL.  Return true iff any new callgraph edges were discovered as a
   result of inlining.  */

static bool
cgraph_mark_inline_edge (struct cgraph_edge *e, bool update_original,
			 VEC (cgraph_edge_p, heap) **new_edges)
{
  int old_insns = 0, new_insns = 0;
  struct cgraph_node *to = NULL, *what;
  struct cgraph_edge *curr = e;

  if (e->callee->inline_decl)
    cgraph_redirect_edge_callee (e, cgraph_node (e->callee->inline_decl));

  gcc_assert (e->inline_failed);
  e->inline_failed = NULL;

  if (!e->callee->global.inlined)
    DECL_POSSIBLY_INLINED (e->callee->decl) = true;
  e->callee->global.inlined = true;

  cgraph_clone_inlined_nodes (e, true, update_original);

  what = e->callee;

  /* Now update size of caller and all functions caller is inlined
     into, as well as the max_bb_count.  */
  for (;e && !e->inline_failed; e = e->caller->callers)
    {
      old_insns = e->caller->global.insns;
      new_insns = cgraph_estimate_size_after_inlining (1, e->caller,
						       what);
      gcc_assert (new_insns >= 0);
      to = e->caller;
      to->global.insns = new_insns;

      if (to->max_bb_count < e->callee->max_bb_count)
	to->max_bb_count = e->callee->max_bb_count;
    }
  gcc_assert (what->global.inlined_to == to);
  if (new_insns > old_insns)
    overall_insns += new_insns - old_insns;
  ncalls_inlined++;

  if (dump_file)
    {
      fprintf (dump_file, "INLINE: ");
      dump_inlining_decision (dump_file, curr);
      fprintf (dump_file, "\n");
    }

  if (flag_indirect_inlining)
    return ipa_propagate_indirect_call_infos (curr, new_edges);
  else
    return false;
}

/* Mark all calls of EDGE->CALLEE inlined into EDGE->CALLER.
   Return following unredirected edge in the list of callers
   of EDGE->CALLEE  */

static struct cgraph_edge *
cgraph_mark_inline (struct cgraph_edge *edge)
{
  struct cgraph_node *to = edge->caller;
  struct cgraph_node *what = edge->callee;
  struct cgraph_edge *e, *next;

  gcc_assert (!gimple_call_cannot_inline_p (edge->call_stmt));
  /* Look for all calls, mark them inline and clone recursively
     all inlined functions.  */
  for (e = what->callers; e; e = next)
    {
      next = e->next_caller;
      if (e->caller == to && e->inline_failed
          /* Skip fake edge.  */
          && e->call_stmt)
	{
          cgraph_mark_inline_edge (e, true, NULL);
	  if (e == edge)
	    edge = next;
	}
    }

  return edge;
}

/* Estimate the growth caused by inlining NODE into all callees.
   Return value is the average expected growth per callsite.  */

static int
cgraph_estimate_growth (struct cgraph_node *node)
{
  int growth = 0, ncalls = 0;
  struct cgraph_edge *e;
  bool self_recursive = false;

  if (node->global.estimated_average_growth != INT_MIN)
    return node->global.estimated_average_growth;

  for (e = node->callers; e; e = e->next_caller)
    {
      if (e->caller == node)
        self_recursive = true;
      if (e->inline_failed)
	{
	  growth += (cgraph_estimate_size_after_inlining (1, e->caller, node)
		     - e->caller->global.insns);
	  ncalls++;
	}
    }

  /* ??? Wrong for non-trivially self recursive functions or cases where
     we decide to not inline for different reasons, but it is not big deal
     as in that case we will keep the body around, but we will also avoid
     some inlining.  */
  if (!self_recursive)
    {
      int emitted_size = (node->global.insns
			  + PARAM_VALUE(PARAM_INLINE_FUNCTION_SIZE_ADJUSTMENT));
      if (!node->needed && !DECL_EXTERNAL (node->decl))
	growth -= emitted_size;
      else if (node->address_taken)
	growth -= ((100.0
		    - PARAM_VALUE (PARAM_INLINE_ADDRESS_TAKEN_FUNCTION_EMIT_PROBABILITY))
		   * emitted_size) / 100;
      else
	growth -= ((100.0
		    - PARAM_VALUE (PARAM_INLINE_ADDRESS_NOT_TAKEN_FUNCTION_EMIT_PROBABILITY))
		   * emitted_size) / 100;
    }

  if (ncalls > 0)
    /* If growth before averaging is less than zero, we'd like the
       average to be less than zero because some heuristics cue off
       this less-than-zero growth condition, so subtract NCALLS - 1 to
       ensure that -1/NCALLS rounds down to -1.  */
    growth = (growth - (ncalls - 1)) / ncalls;

  node->global.estimated_average_growth = growth;
  return growth;
}

/* Return true if there exists a path from FROM to TO in the call
   graph which consists entirely of functions with the always_inline
   attribute.  This is trivially true if FROM calls TO.  MAX_DEPTH
   limits search depth to avoid infinite recursion and otherwise
   expensive searches.  */

static bool
always_inline_path (struct cgraph_node *from, struct cgraph_node *to,
		    int max_depth)
{
  struct cgraph_edge *e;

  if (max_depth == 0)
    return false;

  for (e = from->callees; e; e = e->next_callee)
    {
      if (e->callee == to)
	return true;

      if (!e->inline_failed
	  || lookup_attribute ("always_inline", DECL_ATTRIBUTES (e->callee->decl)))
	{
	  /* Edge is an inlined edge or callee is always_inline.
	     Continue search down edge.  Only decrement MAX_DEPTH if
	     entering a new function.  */
	  if (always_inline_path(e->callee, to,
				 e->inline_failed ? max_depth - 1 : max_depth))
	    return true;
	}
    }
  return false;
}

/* Return false when inlining WHAT into TO is not good idea as it
   would violate growth limits or other constraints.  When ONE_ONLY is
   true, assume that only one call site is going to be inlined,
   otherwise figure out how many call sites in TO calls WHAT and
   verify that all can be inlined.
   */

static bool
cgraph_check_inline_constraints (struct cgraph_node *to,
				 struct cgraph_node *what,
				 const char **reason, bool one_only)
{
  int times = 0;
  struct cgraph_edge *e;
  int newsize;
  int limit;
  HOST_WIDE_INT stack_size_limit, inlined_stack;

  if (one_only)
    times = 1;
  else
    for (e = to->callees; e; e = e->next_callee)
      if (e->callee == what)
	times++;

  if (to->global.inlined_to)
    to = to->global.inlined_to;

  /* When inlining large function body called once into small function,
     take the inlined function as base for limiting the growth.  */
  if (inline_summary (to)->self_insns > inline_summary(what)->self_insns)
    limit = inline_summary (to)->self_insns;
  else
    limit = inline_summary (what)->self_insns;

  limit += limit * PARAM_VALUE (PARAM_LARGE_FUNCTION_GROWTH) / 100;

  /* Check the size after inlining against the function limits.  But allow
     the function to shrink if it went over the limits by forced inlining.  */
  newsize = cgraph_estimate_size_after_inlining (times, to, what);
  if (newsize >= to->global.insns
      && newsize > PARAM_VALUE (PARAM_LARGE_FUNCTION_INSNS)
      && newsize > limit)
    {
      if (reason)
        *reason = N_("--param large-function-growth limit reached");
      return false;
    }

  stack_size_limit = inline_summary (to)->estimated_self_stack_size;

  stack_size_limit += stack_size_limit * PARAM_VALUE (PARAM_STACK_FRAME_GROWTH) / 100;

  if (flag_pessimistic_inline_stack_limit)
    inlined_stack = (to->global.estimated_stack_size_pessimistic
                     + what->global.estimated_stack_size_pessimistic);
  else
    inlined_stack = (to->global.stack_frame_offset
                     + inline_summary (to)->estimated_self_stack_size
                     + what->global.estimated_stack_size);
  if (inlined_stack  > stack_size_limit
      && inlined_stack > PARAM_VALUE (PARAM_LARGE_STACK_FRAME))
    {
      if (reason)
        *reason = N_("--param large-stack-frame-growth limit reached");
      return false;
    }

  /* Not inlining a call to a function marked always_inline is an
     error.  If TO is marked always_inline, verify that inlining WHAT
     into TO will not result in the impossible-to-resolve situation of
     TO calling itself directly or via a chain of always_inline
     functions.  */
  if (lookup_attribute ("always_inline", DECL_ATTRIBUTES (to->decl))
      && always_inline_path (what, to, 10))
      {
	if (reason)
	  *reason = N_("inlining would result in recursive always_inline function");
	return false;
      }

  return true;
}

/* Return false when inlining EDGE is not good idea.  Checks for hot
   component growth and calls cgraph_check_inline_constraints for all other
   checks.  */

static bool
cgraph_check_inline_constraints_edge (struct cgraph_edge *edge, const char **reason)
{
  if (flag_limit_hot_components && n_hot_components
      && cgraph_maybe_hot_edge_p (edge))
    {
      struct hot_component_list *p;

      for (p = *(hot_component_list_for_node (edge->caller)); p; p = p->next)
        {
          int newsize = p->component->size
            + hot_component_growth_after_inlining (edge, p->component->uid);
          int limit = p->component->original_size;

          limit += limit * PARAM_VALUE (PARAM_HOT_COMPONENT_GROWTH) / 100;
          if (newsize > p->component->size
              && newsize > PARAM_VALUE (PARAM_LARGE_HOT_COMPONENT_INSNS)
              && newsize > limit)
            {
              if (reason)
                *reason = N_("--param hot-component-growth limit reached");
              return false;
            }
        }
    }
  return cgraph_check_inline_constraints (edge->caller, edge->callee,
					  reason, true);
}

/* Return true when function N is small enough to be inlined.  */

bool
cgraph_default_inline_p (struct cgraph_node *n, const char **reason)
{
  tree decl = n->decl;
  const char *overlimit_reason;
  int limit;

  if (n->inline_decl)
    decl = n->inline_decl;
  if (!flag_inline_small_functions && !DECL_DECLARED_INLINE_P (decl))
    {
      if (reason)
	*reason = N_("function not inline candidate");
      return false;
    }

  if (!DECL_STRUCT_FUNCTION (decl)->cfg)
    {
      if (reason)
	*reason = N_("function body not available");
      return false;
    }

  if (DECL_DECLARED_INLINE_P (decl))
    {
      limit = MAX_INLINE_INSNS_SINGLE;
      overlimit_reason = N_("--param max-inline-insns-single limit reached");
    }
  else
    {
      limit = MAX_INLINE_INSNS_AUTO;
      overlimit_reason = N_("--param max-inline-insns-auto limit reached");
    }

  /* If profile information is available, expand maximum size limits.  */
  if (profile_info_available_p ())
    limit = ((limit
              * (100 + PARAM_VALUE (PARAM_INLINE_LIMIT_INCREASE_WITH_PROFILE)))
             / 100);

  if (n->global.insns >= limit)
    {
      if (reason)
        *reason = overlimit_reason;
      return false;
    }

  return true;
}

/* Return true when inlining WHAT would create recursive inlining.
   We call recursive inlining all cases where same function appears more than
   once in the single recursion nest path in the inline graph.  */

static bool
cgraph_recursive_inlining_p (struct cgraph_node *to,
			     struct cgraph_node *what,
			     const char **reason)
{
  bool recursive;
  if (to->global.inlined_to)
    recursive = what->decl == to->global.inlined_to->decl;
  else
    recursive = what->decl == to->decl;
  /* Marking recursive function inline has sane semantic and thus we should
     not warn on it.  */
  if (recursive && reason)
    *reason = (what->local.disregard_inline_limits
	       ? N_("recursive inlining") : "");
  return recursive;
}

/* Return true if FUNCDECL is a function with fixed
   argument list.  */

static bool
fixed_arg_function_p (tree fndecl)
{
  tree fntype = TREE_TYPE (fndecl);
  return (TYPE_ARG_TYPES (fntype) == 0
          || (TREE_VALUE (tree_last (TYPE_ARG_TYPES (fntype)))
              == void_type_node));
}

/* For profile collection with flag_dyn_ipa (LIPO), we always
   want to inline comdat functions for the following reasons:
   1) Functions in comdat may be actually defined in a different
   module (depending on how linker picks). This results in a edge
   from one module to another module in the dynamic callgraph.
   The edge is false and result in unnecessary module grouping.
   2) The profile counters in comdat functions are not 'comdated'
   -- which means each copy of the same comdat function has its
   own set of counters. With inlining, we are actually splitting
   the counters and make the profile information 'context sensitive',
   which is a good thing.
   3) During profile-use pass of LIPO (flag_dyn_ipa == 1),
   the pre-tree_profile inline decisions have to be the same as the
   profile-gen pass (otherwise coverage mismatch will occur). Due to
   this reason, it is better for each module to 'use' the comdat copy
   of its own. The only way to get profile data for the copy is to
   inline the copy in profile-gen phase.
   TODO: For indirectly called comdat functions, the above issues
   still exist. */

static bool
better_inline_comdat_function_p (struct cgraph_node *node)
{
  return (profile_arc_flag && flag_dyn_ipa
          && DECL_COMDAT (node->decl)
          && node->global.insns <= PARAM_VALUE (PARAM_MAX_INLINE_INSNS_SINGLE)
          && fixed_arg_function_p (node->decl));
}


/* Compute the inlining priority for EDGE.  The value is generally
   computed as the growth of inlining the callsite divided by the
   frequency of the callsite.  Lower values are higher priority.  */

static int
cgraph_edge_priority (struct cgraph_edge *edge)
{
  /* GROWTH is the minimum of the code growth of inlining the callsite
     and the average growth of inlining all the callsite of the
     callee.  Including the average callsite growth factors in the
     potential benefit of not having to emit the function body should
     all callsites of the callee be inlined and the function is not
     needed.  */
  int growth = MIN (cgraph_estimate_size_after_inlining (1, edge->caller,
							 edge->callee)
		    - edge->caller->global.insns,
		    cgraph_estimate_growth (edge->callee));
  int priority;

  /* Always prefer inlining saving code size, and inline comdat
     functions with LIPO.  */
  if (growth <= 0
      || better_inline_comdat_function_p (edge->callee))
    priority = 0;
  else
    {
      /* FREQ_DIVISOR is some estimate of the frequency of the
	 callsite.  The value can range from 0 to 1.0.  */
      double freq_divisor;

      if (max_count)
	{
	  /* When profiling is available, use the execution count of the
	     callsite as a fraction of the maximum count.  */
	  struct cgraph_node *caller = (edge->caller->global.inlined_to
					? edge->caller->global.inlined_to
					: edge->caller);
	  if (flag_sample_profile
	      && get_total_count_edge (edge, cgraph_node_name (caller)) > 0)
	    /* When using sample profile, if the function is inlined during the
	       profiling run, we will give it higher priority to be inlined.  */
	    freq_divisor = 1.0;
	  else
	    freq_divisor = (double)edge->count / max_count;
	}
      else if (flag_guess_branch_prob)
	/* When function local profile is available, base priorities on
	   estimated frequency, so we optimize for overall frequency of
	   inlined calls.  This is not too accurate since while the call
	   might be frequent within function, the function itself is
	   infrequent.  */
	freq_divisor = (double)edge->frequency / CGRAPH_FREQ_MAX;
      else
	{
	  /* When function local profile is not available or it does not
	     give useful information (ie frequency is zero), base the
	     frequency upon the loop nest where each loop is estimated to
	     be executed twice.  The nest depth is capped at a
	     constant so the maximum FREQ_DIVISOR value is 1.0.  */
	  int nest = MIN (edge->loop_nest, 8);
	  freq_divisor = 1.0 / (1 << (8 - nest));
	}

      if ((freq_divisor <= 0.0)
	  || (growth / freq_divisor > INT_MAX - 1))
	/* Limit priority to one less than INT_MAX to leave room for
	   incrementing priority due to recursive inlining below.  */
	priority = INT_MAX - 1;
      else
	priority = (int) (growth / freq_divisor);

      /* Make recursive inlining happen always after other inlining is done.  */
      if (cgraph_recursive_inlining_p (edge->caller, edge->callee, NULL))
	priority += 1;
    }
  gcc_assert (priority >= 0);
  return priority;
}

/* Compute a key for EDGE for the priority heap of edges to inline.
   The most-significant bits of the key are the callsite priority.  To
   improve the stability of inlining decisions, the least-significant
   bits are the caller and callee sizes.  Callsites with identical key
   values are essentially selected in arbitrary order during inlining,
   so seemingly innocuous source code changes can affect inlining
   decisions significantly by changing the inlining order of callsites
   with the same key.  Adding tie-breakers (caller and callee sizes)
   reduces the incidence of such cases.  */

static fibheapkey_t
cgraph_edge_priority_key (struct cgraph_edge *edge)
{
  int priority = cgraph_edge_priority (edge);
  int shift = 0;

  /* To make room for the callee and caller sizes (prioirity tie
     breakers), the priority must be packed into 16-bits.  Rather than
     truncate or clip the value, the priority is compressed.  Values
     greater than or equal to 2**12 are right-shifted by one or more
     bits.  This is represented in 16-bits with 2 fields: the value to
     shift (lower 12 bits), and the amount to shift (upper 4 bits).
     This compressed value increases monotonically as the priority
     increases.  Priorities higher than 2**27 are clipped, but the
     priority is never that high for any callsite that has a chance of
     being inlined  */
  gcc_assert (priority >= 0);
  while ((priority >= (1 << 12)) && (shift < 16))
    {
      priority >>= 1;
      shift++;
    }
  if (shift == 16)
    priority = (1 << 16) - 1;
  else
    priority = (shift << 12) + priority;

  return (INT_MIN
	  + (priority << 16)
	  + (MIN (255, edge->callee->global.insns) << 8)
	  + MIN (255, edge->caller->global.insns));
}

static int
key_to_priority (fibheapkey_t key)
{
  int value = (key >> 16) - (INT_MIN >> 16);
  int shift;
  gcc_assert ((value >= 0) && (value < (1 << 16)));
  shift = (value >> 12) & 0xf;
  value = value & 0xfff;
  return value << shift;
}

/* Recompute heap nodes for each of caller edge.  */

static void
update_caller_keys (fibheap_t heap, struct cgraph_node *node,
		    bitmap updated_nodes)
{
  struct cgraph_edge *edge;
  const char *failed_reason;

  if (!node->local.inlinable || node->local.disregard_inline_limits
      || node->global.inlined_to)
    return;
  if (bitmap_bit_p (updated_nodes, node->uid))
    return;
  bitmap_set_bit (updated_nodes, node->uid);
  node->global.estimated_average_growth = INT_MIN;

  if (!node->local.inlinable)
    return;
  /* Prune out edges we won't inline into anymore.  */
  if (!cgraph_default_inline_p (node, &failed_reason) 
      && !better_inline_comdat_function_p (node))
    {
      for (edge = node->callers; edge; edge = edge->next_caller)
	if (edge->aux)
	  {
	    fibheap_delete_node (heap, (fibnode_t) edge->aux);
	    edge->aux = NULL;
	    if (edge->inline_failed)
	      edge->inline_failed = failed_reason;
	  }
      return;
    }

  for (edge = node->callers; edge; edge = edge->next_caller)
    if (edge->inline_failed)
      {
	fibheapkey_t new_key = cgraph_edge_priority_key (edge);
	if (edge->aux)
	  {
	    fibnode_t n = (fibnode_t) edge->aux;
	    gcc_assert (n->data == edge);
	    if (n->key == new_key)
	      continue;

	    /* fibheap_replace_key only increase the keys.  */
	    if (new_key < n->key)
	      {
		fibheap_replace_key (heap, n, new_key);
		gcc_assert (n->key == new_key);
		continue;
	      }
	    fibheap_delete_node (heap, (fibnode_t) edge->aux);
	  }
	edge->aux = fibheap_insert (heap, new_key, edge);
      }
}

/* Recompute heap nodes for each of caller edges of each of callees.  */

static void
update_callee_keys (fibheap_t heap, struct cgraph_node *node,
		    bitmap updated_nodes)
{
  struct cgraph_edge *e;
  node->global.estimated_average_growth = INT_MIN;

  for (e = node->callees; e; e = e->next_callee)
    if (e->inline_failed)
      update_caller_keys (heap, e->callee, updated_nodes);
    else if (!e->inline_failed)
      update_callee_keys (heap, e->callee, updated_nodes);
}

/* Enqueue all recursive calls from NODE into priority queue depending on
   how likely we want to recursively inline the call.  */

static void
lookup_recursive_calls (struct cgraph_node *node, struct cgraph_node *where,
			fibheap_t heap)
{
  static int priority;
  struct cgraph_edge *e;
  for (e = where->callees; e; e = e->next_callee)
    if (e->callee == node)
      {
	/* When profile feedback is available, prioritize by expected number
	   of calls.  Without profile feedback we maintain simple queue
	   to order candidates via recursive depths.  */
        fibheap_insert (heap,
			!max_count ? priority++
		        : -(e->count / ((max_count + (1<<24) - 1) / (1<<24))),
		        e);
      }
  for (e = where->callees; e; e = e->next_callee)
    if (!e->inline_failed)
      lookup_recursive_calls (node, e->callee, heap);
}

/* Create a clone of NODE to use in recursive inlining.  */

static struct cgraph_node*
create_recursive_clone (struct cgraph_node *node)
{
  struct cgraph_node *clone;
  struct cgraph_edge *e;

  clone = cgraph_clone_node (node, node->count, CGRAPH_FREQ_BASE, 1, false);
  clone->needed = true;
  for (e = clone->callees; e; e = e->next_callee)
    if (!e->inline_failed)
      cgraph_clone_inlined_nodes (e, true, false);

  return clone;
}

/* Delete the cloned node NODE used for recursive inlining.  */

static void
delete_recursive_clone (struct cgraph_node *clone)
{
  struct cgraph_node *node, *next;

  for (node = cgraph_nodes; node != clone; node = next)
    {
      next = node->next;
      if (node->global.inlined_to == clone)
	cgraph_remove_node (node);
    }
  cgraph_remove_node (clone);
}

/* Decide on recursive inlining: in the case function has recursive calls,
   inline until body size reaches given argument.  If any new indirect edges
   are discovered in the process, add them to *NEW_EDGES, unless NEW_EDGES
   is NULL.  */

static bool
cgraph_decide_recursive_inlining (struct cgraph_node *node,
				  VEC (cgraph_edge_p, heap) **new_edges)
{
  int limit = PARAM_VALUE (PARAM_MAX_INLINE_INSNS_RECURSIVE_AUTO);
  int max_depth = PARAM_VALUE (PARAM_MAX_INLINE_RECURSIVE_DEPTH_AUTO);
  int probability = PARAM_VALUE (PARAM_MIN_INLINE_RECURSIVE_PROBABILITY);
  fibheap_t heap;
  struct cgraph_node *master_clone;
  int depth = 0;
  int n = 0;

  if (optimize_function_for_size_p (DECL_STRUCT_FUNCTION (node->decl))
      || (!flag_inline_functions && !DECL_DECLARED_INLINE_P (node->decl)))
    return false;

  if (DECL_DECLARED_INLINE_P (node->decl))
    {
      limit = PARAM_VALUE (PARAM_MAX_INLINE_INSNS_RECURSIVE);
      max_depth = PARAM_VALUE (PARAM_MAX_INLINE_RECURSIVE_DEPTH);
    }

  /* Make sure that function is small enough to be considered for inlining.  */
  if (!max_depth
      || cgraph_estimate_size_after_inlining (1, node, node)  >= limit)
    return false;
  heap = fibheap_new ();
  lookup_recursive_calls (node, node, heap);
  if (fibheap_empty (heap))
    {
      fibheap_delete (heap);
      return false;
    }

  if (dump_file)
    fprintf (dump_file, 
	     "  Performing recursive inlining on %s\n",
	     cgraph_node_name (node));

  /* We need original clone to copy around.  */
  master_clone = create_recursive_clone (node);

  /* Do the inlining and update list of recursive call during process.  */
  while (!fibheap_empty (heap)
	 && (cgraph_estimate_size_after_inlining (1, node, master_clone)
	     <= limit))
    {
      struct cgraph_edge *curr
	= (struct cgraph_edge *) fibheap_extract_min (heap);
      struct cgraph_node *cnode;

      depth = 1;
      for (cnode = curr->caller;
	   cnode->global.inlined_to; cnode = cnode->callers->caller)
	if (node->decl == curr->callee->decl)
	  depth++;
      if (depth > max_depth)
	{
          if (dump_file)
	    fprintf (dump_file, 
		     "   maximal depth reached\n");
	  continue;
	}

      if (max_count)
	{
          if (!cgraph_maybe_hot_edge_p (curr))
	    {
	      if (dump_file)
		fprintf (dump_file, "   Not inlining cold call\n");
	      continue;
	    }
          if (node->count == 0 || (curr->count * 100 / node->count < probability))
	    {
	      if (dump_file)
		fprintf (dump_file, 
			 "   Probability of edge is too small\n");
	      continue;
	    }
	}

      if (!dbg_cnt (inl))
        continue;

      if (dump_file)
	{
	  fprintf (dump_file, 
		   "   Inlining call of depth %i", depth);
	  if (node->count)
	    {
	      fprintf (dump_file, " called approx. %.2f times per call",
		       (double)curr->count / node->count);
	    }
	  fprintf (dump_file, "\n");
	}
      cgraph_redirect_edge_callee (curr, master_clone);
      cgraph_mark_inline_edge (curr, false, new_edges);
      lookup_recursive_calls (node, curr->callee, heap);
      n++;
    }
  if (!fibheap_empty (heap) && dump_file)
    fprintf (dump_file, "    Recursive inlining growth limit met.\n");

  fibheap_delete (heap);
  if (dump_file)
    fprintf (dump_file, 
	     "\n   Inlined %i times, body grown from %i to %i insns\n", n,
	     master_clone->global.insns, node->global.insns);

  /* Remove master clone we used for inlining.  We rely that clones inlined
     into master clone gets queued just before master clone so we don't
     need recursion.  */
  delete_recursive_clone (master_clone);

  /* FIXME: Recursive inlining actually reduces number of calls of the
     function.  At this place we should probably walk the function and
     inline clones and compensate the counts accordingly.  This probably
     doesn't matter much in practice.  */
  return n > 0;
}

/* Set inline_failed for all callers of given function to REASON.  */

static void
cgraph_set_inline_failed (struct cgraph_node *node, const char *reason)
{
  struct cgraph_edge *e;

  if (dump_file)
    fprintf (dump_file, "Inlining failed: %s\n", reason);
  for (e = node->callers; e; e = e->next_caller)
    if (e->inline_failed)
      e->inline_failed = reason;
}

/* Given whole compilation unit estimate of INSNS, compute how large we can
   allow the unit to grow.  */
static int
compute_max_insns (int insns)
{
  int max_insns = insns;
  if (max_insns < PARAM_VALUE (PARAM_LARGE_UNIT_INSNS))
    max_insns = PARAM_VALUE (PARAM_LARGE_UNIT_INSNS);

  return ((HOST_WIDEST_INT) max_insns
	  * (100 + PARAM_VALUE (PARAM_INLINE_UNIT_GROWTH)) / 100);
}

/* Compute priority keys of all edges in NEW_EDGES and add them to the
   HEAP.  */
static void
add_new_edges_to_heap (fibheap_t heap, VEC (cgraph_edge_p, heap) *new_edges)
{
  while (VEC_length (cgraph_edge_p, new_edges) > 0)
    {
      struct cgraph_edge *edge = VEC_pop (cgraph_edge_p, new_edges);

      gcc_assert (!edge->aux);
      edge->aux = fibheap_insert (heap, cgraph_edge_priority_key (edge), edge);
    }
}


/* We use greedy algorithm for inlining of small functions:
   All inline candidates are put into prioritized heap based on estimated
   growth of the overall number of instructions and then update the estimates.

   INLINED and INLINED_CALEES are just pointers to arrays large enough
   to be passed to cgraph_inlined_into and cgraph_inlined_callees.  */

static void
cgraph_decide_inlining_of_small_functions (void)
{
  struct cgraph_node *node;
  struct cgraph_edge *edge;
  const char *failed_reason;
  fibheap_t heap = fibheap_new ();
  bitmap updated_nodes = BITMAP_ALLOC (NULL);
  int min_insns, max_insns;
  VEC (cgraph_edge_p, heap) *new_indirect_edges = NULL;

  if (flag_indirect_inlining)
    new_indirect_edges = VEC_alloc (cgraph_edge_p, heap, 8);

  if (dump_file)
    fprintf (dump_file, "\nDeciding on smaller functions:\n");

  /* Put all inline candidates into the heap.  */

  for (node = cgraph_nodes; node; node = node->next)
    {
      if (!node->local.inlinable || !node->callers
	  || node->local.disregard_inline_limits)
	continue;

      if (dump_file)
	fprintf (dump_file, "Considering inline candidate %s.\n",
		 cgraph_node_name (node));

      node->global.estimated_average_growth = INT_MIN;
      if (!cgraph_default_inline_p (node, &failed_reason) &&
          !better_inline_comdat_function_p (node))
	{
	  cgraph_set_inline_failed (node, failed_reason);
	  continue;
	}

      for (edge = node->callers; edge; edge = edge->next_caller)
	if (edge->inline_failed)
	  {
	    gcc_assert (!edge->aux);
	    edge->aux = fibheap_insert (heap,
					cgraph_edge_priority_key (edge), edge);
	  }
    }

  max_insns = compute_max_insns (overall_insns);
  min_insns = overall_insns;

  if (dump_file)
    {
      fprintf (dump_file, "Initial max_insns = %d\n", max_insns);
      fprintf (dump_file, "Initial min_insns = %d\n", min_insns);
    }

  while (overall_insns <= max_insns && !fibheap_empty (heap))
    {
      int old_insns = overall_insns, growth;
      fibheapkey_t key;
      struct cgraph_node *caller, *callee;
      const char *not_good = NULL;

      key = fibheap_min_key (heap);
      edge = (struct cgraph_edge *) fibheap_extract_min (heap);
      gcc_assert (edge->aux);
      edge->aux = NULL;
      if (!edge->inline_failed)
	continue;

      growth =
	(cgraph_estimate_size_after_inlining (1, edge->caller, edge->callee)
	 - edge->caller->global.insns);

      /* If fibheap keys are updated properly, these values should
	 always be identical.  */
      gcc_assert (key == cgraph_edge_priority_key (edge));

      if (dump_file)
	{
	  fprintf (dump_file,
		   "\nConsidering %s with %i insns\n",
		   cgraph_node_name (edge->callee),
		   edge->callee->global.insns);
	  fprintf (dump_file,
		   " to be inlined into %s\n"
		   " Estimated average growth after inlined into all callees is %+i insns.\n"
		   " Estimated priority is %i, frequency %.2f.\n",
		   cgraph_node_name (edge->caller),
		   cgraph_estimate_growth (edge->callee), key_to_priority (key),
		   edge->frequency / (double)CGRAPH_FREQ_BASE);
	  if (edge->count)
	    fprintf (dump_file," Called "HOST_WIDEST_INT_PRINT_DEC"x\n", edge->count);
	}


      /* When not having profile info ready we don't weight by any way the
         position of call in procedure itself.  This means if call of
	 function A from function B seems profitable to inline, the recursive
	 call of function A in inline copy of A in B will look profitable too
	 and we end up inlining until reaching maximal function growth.  This
	 is not good idea so prohibit the recursive inlining.

	 ??? When the frequencies are taken into account we might not need this
	 restriction.

	 We need to be cureful here, in some testcases, e.g. directivec.c in
	 libcpp, we can estimate self recursive function to have negative growth
	 for inlining completely.
	 */
      if (!edge->count && !(flag_sample_profile && get_total_count_edge (edge,
            cgraph_node_name (edge->caller->global.inlined_to ?
                              edge->caller->global.inlined_to :
                              edge->caller)) > 0))
	{
	  struct cgraph_node *where = edge->caller;
	  while (where->global.inlined_to)
	    {
	      if (where->decl == edge->callee->decl)
		break;
	      where = where->callers->caller;
	    }
	  if (where->global.inlined_to)
	    {
	      edge->inline_failed
		= (edge->callee->local.disregard_inline_limits ? N_("recursive inlining") : "");
	      if (dump_file)
		fprintf (dump_file, " inline_failed:Recursive inlining performed only for function itself.\n");
	      continue;
	    }
	}

      if (!cgraph_maybe_hot_edge_p (edge))
	{
	  if (max_count && PARAM_VALUE (PARAM_MIN_COUNT_FRACTION_FOR_INLINE_COLD))
	    {
	      /* Even if an edge is cold and the function entry is
		 cold, the callee may contain hot code.  In this case,
		 inlining can be advantageous because important
		 context can be propagated to the hot code.  This edge
		 is considered for inlining only if it is one of the
		 more likely callers of the hot function and the
		 function contains sufficiently hot code.  More
		 precisely, if the estimated maximum count in the
		 callee along the edge is greater than the fraction of
		 global maximum count as defined with
		 PARAM_MIN_COUNT_FRACTION_FOR_INLINE_COLD, then the
		 edge is still an inline candidate..  */
	      if (edge->callee->count &&
		  ((int)((double)edge->count * edge->callee->max_bb_count
			 / edge->callee->count)
		   >= (profile_info->sum_max
		       / PARAM_VALUE (PARAM_MIN_COUNT_FRACTION_FOR_INLINE_COLD))))
		{
		  if (dump_file)
		    fprintf (dump_file, "Callsite is cold, but still a "
			     "candidate because callee is sufficiently hot.\n");
		}
	      else
		not_good = N_("call is unlikely and code size would grow");
	    }
	  else
	    not_good = N_("call is unlikely and code size would grow");
	}
      if (!flag_inline_functions
	  && !DECL_DECLARED_INLINE_P (edge->callee->decl)
	  && (key_to_priority (key)
	      > PARAM_VALUE (PARAM_INLINE_PRIORITY_THRESHOLD)))
 	not_good = N_("function not declared inline, code size would grow, "
		      "and priority too low");
      if (optimize_function_for_size_p (DECL_STRUCT_FUNCTION(edge->caller->decl)))
 	not_good = N_("optimizing for size and code size would grow");
      if (not_good && growth > 0 && cgraph_estimate_growth (edge->callee) > 0)
	{
          if (!cgraph_recursive_inlining_p (edge->caller, edge->callee,
				            &edge->inline_failed))
	    {
	      edge->inline_failed = not_good;
	      if (dump_file)
		fprintf (dump_file, " inline_failed:%s.\n", edge->inline_failed);
	    }
	  continue;
	}
      if (!cgraph_default_inline_p (edge->callee, &edge->inline_failed) 
          && !better_inline_comdat_function_p (edge->callee))
	{
          if (!cgraph_recursive_inlining_p (edge->caller, edge->callee,
				            &edge->inline_failed))
	    {
	      if (dump_file)
		fprintf (dump_file, " inline_failed:%s.\n", edge->inline_failed);
	    }
	  continue;
	}
      if (!tree_can_inline_p (edge->caller->decl, edge->callee->decl))
	{
	  gimple_call_set_cannot_inline (edge->call_stmt, true);
	  edge->inline_failed = N_("target specific option mismatch");
	  if (dump_file)
	    fprintf (dump_file, " inline_failed:%s.\n", edge->inline_failed);
	  continue;
	}

      caller = edge->caller;
      if (caller->global.inlined_to)
	caller = caller->global.inlined_to;
      callee = edge->callee;

      if (cgraph_recursive_inlining_p (edge->caller, edge->callee,
				       &edge->inline_failed))
	{
	  if (!cgraph_decide_recursive_inlining (caller,
						 flag_indirect_inlining
						 ? &new_indirect_edges : NULL))
	    continue;
	  if (flag_indirect_inlining)
	    add_new_edges_to_heap (heap, new_indirect_edges);
	}
      else
	{
	  if (gimple_call_cannot_inline_p (edge->call_stmt)
	      || !cgraph_check_inline_constraints_edge (edge, &edge->inline_failed))
	    {
	      if (dump_file)
		fprintf (dump_file, " Not inlining into %s:%s.\n",
			 cgraph_node_name (edge->caller), edge->inline_failed);
	      continue;
	    }

          if (!dbg_cnt (inl))
            continue;

	  cgraph_mark_inline_edge (edge, true, &new_indirect_edges);
	  if (flag_indirect_inlining)
	    add_new_edges_to_heap (heap, new_indirect_edges);
	}

      /* Our profitability metric depends upon local properties of the
	 caller and callee, as well as global properties such as the
	 number of times a function is called.  The priority of edges
	 already in the heap need to be adjusted accordingly.  */

      /* CALLER is the function that the callee is ultimately inlined
	 into, potentially via multiple transitive inlining decisions.
	 It's size likely changed, so update all of its callers.
	 Update it's callees as well because the caller size is used
	 when computing prioirity keys.  Furthermore, updating the
	 callee keys will update callsites within the newly inlined
	 function body.  */
      update_caller_keys (heap, caller, updated_nodes);
      update_callee_keys (heap, caller, updated_nodes);

      /* If the non-inlined body of the callee is still around (CALLEE
	 is not marked as inline), then it must be updated as with
	 INLINED_CALLEE.  Also, because the number of callers of the
	 function which has been inlined has been reduced by one, all
	 callers of the function must be updated.  */
      if (!callee->global.inlined_to)
	{
	  update_callee_keys (heap, callee, updated_nodes);
	  if (caller != callee)
	    /* Add condition to avoid duplicating call to
	       UPDATE_CALLER_KEYS above.  */
	    update_caller_keys (heap, callee, updated_nodes);
	}

      bitmap_clear (updated_nodes);

      if (dump_file)
	{
	  fprintf (dump_file,
		   "%s inlined into %s which now has %i insns, "
                   "net change of %+i insns.\n",
		   cgraph_node_name (edge->callee),
		   cgraph_node_name (edge->caller),
		   edge->caller->global.insns,
		   overall_insns - old_insns);
	}
      if (min_insns > overall_insns)
	{
	  min_insns = overall_insns;
	  max_insns = compute_max_insns (min_insns);

	  if (dump_file)
	    fprintf (dump_file, "New minimal insns reached: %i\n", min_insns);
	}
      if (dump_file)
	{
	  fprintf (dump_file, "max_insns = %d\n", max_insns);
	  fprintf (dump_file, "min_insns = %d\n", min_insns);
	  fprintf (dump_file, "overall_insns = %d\n", overall_insns);
	}
    }
  if (dump_file)
    {
      if (fibheap_empty (heap))
	fprintf (dump_file, "All small function candidates inlined.\n");
      else
	fprintf (dump_file, "Small function priority cutoff is %d.\n",
		 (int) key_to_priority (fibheap_min_key (heap)));
    }
  while ((edge = (struct cgraph_edge *) fibheap_extract_min (heap)) != NULL)
    {
      gcc_assert (edge->aux);
      edge->aux = NULL;
      if (!edge->callee->local.disregard_inline_limits && edge->inline_failed
          && !cgraph_recursive_inlining_p (edge->caller, edge->callee,
				           &edge->inline_failed))
	edge->inline_failed = N_("--param inline-unit-growth limit reached");
    }

  if (new_indirect_edges)
    VEC_free (cgraph_edge_p, heap, new_indirect_edges);
  fibheap_delete (heap);
  BITMAP_FREE (updated_nodes);
}

/* Frees the linked list LST of struct CALLSITE_CHAIN elements.  */

static void
free_callsite_chain (struct callsite_chain *lst)
{
  while (lst)
    {
      struct callsite_chain *p = lst;
      lst = lst->next;
      if (p->function_name)
        free (p->function_name);
      free (p);
    }
}

/* Frees inline plan PLAN.  */

static void
free_inline_plan (struct inline_plan *plan)
{
  struct inline_decision *decision, *tmp;

  decision = plan->decisions;
  while (decision)
    {
      free_callsite_chain (decision->chain);
      tmp = decision->next;
      free (decision);
      decision = tmp;
    }
  free (plan);
}

/* Returns a copy of SRC allocated with XNEW with leading and trailing
   whitespace removed.  */

static char *
new_stripped_string (const char *src)
{
  const char *start = NULL, *end = NULL;
  char *dst;

  for (; *src; src++)
    if (!ISSPACE (*src))
      {
        if (!start)
          start = src;
        end = src + 1;
      }
  dst = XNEWVEC (char, end - start + 1);
  strncpy (dst, start, end - start);
  dst[end - start] = 0;
  return dst;
}

/* Allocates, copies, and returns the substring up to the first
   instance of SEPARATOR in BUF.  Leading and trailing whitespace are
   stripped in the copy.  If NEXT is not NULL, then *NEXT is set to
   the location in buffer immediately after SEPARATOR.  If SEPARATOR
   is not found, then *NEXT is set to NULL and NULL is returned.  */

static char *
new_token_before_separator (char *buf, const char *separator, char **next)
{
  char tmp;
  char *p, *token;

  p = strstr (buf, separator);
  if (!p)
    {
      /* Separator not found in BUF.  */
      if (next)
        *next = NULL;
      return NULL;
    }

  /* Temporarily zero terminate BUF at the beginning of SEPARATOR.  */
  tmp = *p;
  *p = 0;
  token = new_stripped_string (buf);
  *p = tmp;

  /* Set *NEXT to beyond the end of SEPARATOR in BUF.  */
  if (next)
     *next = p + strlen (separator);

  return token;
}

/* Parse the string STR containing an inline chain.  The string
   representation of the chain is the format output by
   DUMP_INLINING_DECISION.  For example:

     FuncA @callsite #1 into FuncB @callsite #5 into ... into FuncZ

   Returns a list of CALLSITE_CHAIN elements.  */

static struct callsite_chain*
parse_inlining_decision (char *str)
{
  struct callsite_chain *chain = NULL;
  char *loc = str;
  bool error = false;

  while (loc)
    {
      char *starting_loc = loc;
      struct callsite_chain *plink = XCNEW (struct callsite_chain);

      plink->next = chain;
      chain = plink;
      plink->function_name =
        new_token_before_separator (starting_loc, "@callsite #", &loc);

      if (loc)
        {
          /* Extract callsite number.  */
          char *callsite_str = new_token_before_separator (loc, "into", &loc);
          if (!loc)
            {
              error = true;
              break;
            }
          plink->callsite_no = atoi (callsite_str);
          free (callsite_str);
        }
      else
        {
          /* No callsite string found, so this must be final function in
             chain.  Final function name is last part of line.  */
          plink->function_name = new_stripped_string (starting_loc);
          plink->callsite_no = 0;
        }
  }

  /* Check for error and at least two elements in list.  */
  if (error || !chain || !chain->next)
    {
      free_callsite_chain (chain);
      chain = NULL;
    }

  return chain;
}


/* Returns the non-inlined cgraph node with unique name NAME.  The
   search skips over cgraph node SKIP if non-NULL.  This is useful
   with recursive inlining which creates a dummy cgraph node clone.

   TODO: This is inefficient.  Probably better to do with a hash.  */

static struct cgraph_node *
find_named_cgraph_node (const char *name, struct cgraph_node *skip)
{
  struct cgraph_node *node;

  for (node = cgraph_nodes; node; node = node->next)
    if (!node->global.inlined_to
        && node != skip
        && node->analyzed
        && node->master_clone == node
        && cgraph_node_matches_unique_name_p (node, name))
      break;
  return node;
}

/* Inlines the edge specified by CHAIN.  *CLONE, if non-NULL, is the
   cloned callee used for recursive inlining.  This mechanism is
   required because a cloned node is used for consecutive recursive
   inlining decisions for edges with the same callee (see
   cgraph_decide_recursive_inlining).  *CLONE is updated to point to
   the new recursive clone if one is created.  In case of error, an
   error string is copied into ERROR_MSG of maximum length
   MSG_LEN.  */

static bool
inline_edge_defined_by_chain (struct callsite_chain *chain,
                              struct cgraph_node **clone,
                              char *error_msg, int msg_len)
{
  struct cgraph_node *caller, *first_caller;
  struct callsite_chain *pchain;
  struct cgraph_edge *edge = NULL;
  char *caller_name = NULL;

  /* The first function in the chain is the enclosing function in
     which the edge is ultimately inlined into.  Find the cgraph node
     for this function, skipping any potential clone.  */
  first_caller = find_named_cgraph_node (chain->function_name, *clone);
  if (!first_caller)
    {
      snprintf (error_msg, msg_len, "no function named %s found",
                chain->function_name);
      return false;
    }
  caller = first_caller;
  caller_name = chain->function_name;

  pchain = chain->next;
  gcc_assert (pchain);
  while (pchain)
    {
      int callsite = 0;

      /* Find last callee.  Edges in the call graph are in the reverse
         order in which they appear in the code, so the edges must be
         walked backwards to find the n-th one.  */
      for (edge = caller->callees;
           edge && edge->next_callee;
           edge = edge->next_callee)
        { /* Nothing. */ }

      if (edge)
        /* Iterating backwards, find the n-th (where n = PCHAIN->CALLSITE_NO)
           call to function PCHAIN->FUNCTION_NAME backwards in the list.  */
        for ( ; edge ; edge = edge->prev_callee)
          if (cgraph_node_matches_unique_name_p (edge->callee,
                                                 pchain->function_name))
            {
              callsite++;
              if (callsite == pchain->callsite_no)
                break;
            }

      if (edge == NULL)
        {
          /* Edge corresponding to the particular callsite defined by
             PCHAIN was not found.  */
          if (callsite == 0)
            snprintf (error_msg, msg_len, "%s does not call %s",
                      caller_name, pchain->function_name);
          else
            snprintf (error_msg, msg_len, "no callsite %d of %s in %s",
                      pchain->callsite_no,
                      pchain->function_name,
                      caller_name);
          return false;
        }

      if (pchain->next)
        /* Edge is not the last in the chain.  Verify that edge has
           been inlined.  */
        if (edge->inline_failed)
          {
            snprintf (error_msg, msg_len,
                      "inlining of callsite %d of %s in %s must precede "
		      "inlining of this edge",
                      pchain->callsite_no,
                      pchain->function_name,
                      caller_name);
            return false;
          }
      caller = edge->callee;
      caller_name = pchain->function_name;

      pchain = pchain->next;
    }

  gcc_assert (edge);
  if (!edge->inline_failed)
    {
      snprintf (error_msg, msg_len, "edge has already been inlined");
      return false;
    }

  if (edge->callee->decl == first_caller->decl)
    {
      /* This is a recursive inlining decision, so the edge needs to
         be directed to a clone of the callee prior to marking the
         edge for inlining.  */
      if (*clone && (*clone)->decl != edge->callee->decl)
        {
          /* Recursive clone exists, but it's a clone of a different
             call graph node from a previous recursive inlining
             decision.  */
          delete_recursive_clone (*clone);
          *clone = NULL;
        }
      if (!*clone)
        /* Create new clone of this node.  */
        *clone = create_recursive_clone (edge->callee);

      cgraph_redirect_edge_callee (edge, *clone);
      cgraph_mark_inline_edge (edge, false, NULL);
    }
  else
    cgraph_mark_inline_edge (edge, true, NULL);

  return true;
}

/* Read an inline plan from FILENAME and return an inline_plan struct
   describing the decisions.

   Each line in the file beginning with "INLINE:" defines a single
   inlined call graph edge.  Lines not beginning with "INLINE:" are
   ignored.  The text after "INLINE:" should be in the same format as
   output by dump_callsite_chain.

   The debugging dumps of the inlining passes include lines defining
   the inlining plan in this format, so the debugging dumps may be
   input as the inlining plan to later replicate the set of inlining
   decisions exactly.  */

static struct inline_plan*
read_inline_plan (const char *filename)
{
  FILE *f;
  unsigned int max_line_len = 4096;
  char *line = XNEWVEC (char, max_line_len);
  int line_no = 1;
  struct inline_decision *last_decision = NULL;
  struct inline_plan *plan;

  f = fopen (filename, "r");
  if (f == (FILE *) 0)
    fatal_error ("can't open inline plan file %s: %m", filename);

  #ifdef ENABLE_CHECKING
  {
    struct cgraph_node *node;
    /* Check for nodes with the same unique names.  */
    for (node = cgraph_nodes; node; node = node->next)
      if (!node->global.inlined_to && node->analyzed)
	{
	  struct cgraph_node *node2;
	  char *node_name = create_unique_cgraph_node_name (node);

	  for (node2 = node->next; node2; node2 = node2->next)
	    if (!node2->global.inlined_to
		&& node2->analyzed
		&& cgraph_node_matches_unique_name_p (node2, node_name))
	      {
		const char *asm_name =
		  IDENTIFIER_POINTER (decl_assembler_name (node->decl));
		const char *asm_name2 =
		  IDENTIFIER_POINTER (decl_assembler_name (node2->decl));

		fatal_error ("cgraph node aliased unique name %s (%s != %s)",
			     node_name, asm_name, asm_name2);
	      }
	  free (node_name);
	}
  }
  #endif

  plan = XCNEW (struct inline_plan);
  while (fgets (line, max_line_len, f) != (char *) 0)
    {
      char *p;

      /* If line doesn't fit in the buffer, then keep doubling the
         size of buffer until it fits.  */
      while (strlen (line) == max_line_len - 1
             && line[max_line_len - 2] != '\n')
        {
          /* Double the size of the line and keep reading.  */
          line = (char *) xrealloc (line, max_line_len * 2);
          fgets (line + max_line_len - 1, max_line_len + 1, f);
          max_line_len *= 2;
        }

      p = line;
      while (*p && ISBLANK (*p))
        p++;

      if (strstr (p, "INLINE:") == p)
        {
          char *stripped = new_stripped_string (p + strlen ("INLINE:"));
          struct inline_decision *decision = XNEW (struct inline_decision);

          decision->line_no = line_no;
          decision->next = NULL;
          decision->chain = parse_inlining_decision (stripped);
          if (!decision->chain)
            fatal_error ("invalid line in inline plan: %s:%d: %s",
                         filename, line_no, line);

          if (last_decision)
            {
              last_decision->next = decision;
              last_decision = decision;
            }
          else
            plan->decisions = last_decision = decision;

          free (stripped);
        }
      line_no++;
    }
  free(line);

  return plan;
}

/* Return the specified plan file, if any, for the current pass.  */

static struct inline_plan_file*
get_plan_file_for_pass (struct opt_pass *pass)
{
  struct inline_plan_file *pfile;
  struct dump_file_info *pinfo;
  const char *pass_suffix;

  if (!inline_plan_files)
    return NULL;

  /* Use the suffix of the dump file to uniquely identify the pass,
     rather than the name of the current pass.  The suffix includes a
     trailing digit to resolve multiple instances of the same pass
     (eg., "einline1" or "einline2").  It is this suffix which is
     matched against the pass name given with
     -finline-plan-<pass>=<file>.  */
  pinfo = get_dump_file_info (pass->static_pass_number);
  if (!pinfo)
    return NULL;

  /* The suffix includes a leading '.'.  Skip it.  */
  pass_suffix = pinfo->suffix + 1;

  /* Find plan for this pass, if any.  */
  for (pfile = inline_plan_files; pfile; pfile = pfile->next)
    if (strcmp (pfile->pass_name, pass_suffix) == 0)
      break;
  return pfile;
}

/* Apply the set of inlining decisions defined by PLAN.  If NODE is
   not NULL then only apply decisions with the function represented by
   NODE.  Returns true if any edges are inlined.  TODO: In the case
   where NODE is non-NULL, this function is inefficient as it examines
   all decisions.  */

static bool
apply_plan (struct inline_plan *plan,
            struct cgraph_node *node)
{
  char msg[256];
  struct inline_decision *p;
  struct cgraph_node *clone = NULL;
  bool inlined = false;

  if (dump_file)
    {
      fprintf (dump_file, "Applying inlining plan from file %s",
               plan->file->filename);
      if (node)
        {
          fprintf (dump_file, "to ");
          dump_unique_cgraph_node_name (dump_file, node);
        }
      fprintf (dump_file, ":\n");
    }

  for (p = plan->decisions; p; p = p->next)
    if (!node
        || cgraph_node_matches_unique_name_p (node, p->chain->function_name))
      {
        if (!inline_edge_defined_by_chain (p->chain, &clone, msg, 256))
          fatal_error ("in inline plan %s:%d: %s",
		       plan->file->filename, p->line_no, msg);
        inlined = true;
      }

  if (clone)
    delete_recursive_clone (clone);

  return inlined;
}

/* Recursive helper function for dumping inlining decisions within a
   function.  */

static void
dump_function_inlining_decisions_1 (FILE *file, struct cgraph_node *node,
				    int indent)
{
  struct cgraph_edge *edge;

  for (edge = node->callees; edge; edge = edge->next_callee)
    {
      int i;
      for (i = 0; i < indent; i++)
	fprintf (file, "    ");
      if (!edge->inline_failed)
	fprintf (file, "[inlined] ");
      fprintf (file, "%s [callsite #%d]",
	       cgraph_node_name (edge->callee),
	       callsite_position (edge));
      if (DECL_DECLARED_INLINE_P (edge->callee->decl))
	fprintf (file, " marked inline");
      else
	fprintf (file, " not marked inline");
      fprintf (file, ", uid %d, size %d, frequency %0.4f",
	       edge->uid, edge->callee->global.insns,
	       (double)edge->frequency / CGRAPH_FREQ_BASE);
      if (max_count)
	fprintf (file, ", count " HOST_WIDEST_INT_PRINT_DEC, edge->count);
      if (edge->inline_failed)
	{
	  if (edge->callee->local.inlinable)
	    fprintf (file, ", priority %d, inline growth %d, all inline growth %d",
		     cgraph_edge_priority (edge),
		     cgraph_estimate_size_after_inlining (1, edge->caller, edge->callee)
		     - edge->caller->global.insns,
		     cgraph_estimate_growth (edge->callee));
	  if (flag_dyn_ipa)
	    {
	      /* For LIPO, if the edge is not entirely within the
		 main module, label it as in an auxilliary module or
		 as crossmodule.  */
		unsigned caller_id = cgraph_get_module_id (edge->caller->decl);
		unsigned callee_id = cgraph_get_module_id (edge->callee->decl);
		if (caller_id == callee_id)
		  {
		    if (caller_id != primary_module_id)
		      fprintf (file, ", aux module id=%u", caller_id);
		  }
		else
		  {
		    /* This is a cross module edge. */
		    fprintf (file, ", crossmodule: ");
		    if (caller_id == primary_module_id)
 		      fprintf (file, "main -> ");
		    else
 		      fprintf (file, "%u -> ", caller_id);
		    if (callee_id == primary_module_id)
 		      fprintf (file, "main");
		    else
 		      fprintf (file, "%u", callee_id);
		  }
	    }
	  fprintf (file, ", inlining failed: %s", edge->inline_failed);
	}
      fprintf (file, "\n");

      if (!edge->inline_failed)
	dump_function_inlining_decisions_1 (file, edge->callee, indent + 1);
    }
}

/* Dump inlining decisions for all callsites in NODE to FILE.  */

static void
dump_function_inlining_decisions (FILE *file, struct cgraph_node *node)
{
  fprintf (file, "%s, uid %d, size %d, %s",
	   cgraph_node_name (node), node->uid, node->global.insns,
	   function_frequency_string (node));
  if (max_count)
    fprintf (file, "count " HOST_WIDEST_INT_PRINT_DEC, node->count);
  if (flag_dyn_ipa && (cgraph_get_module_id (node->decl) != primary_module_id))
    fprintf (file, ", aux module id %u", cgraph_get_module_id (node->decl));
  fprintf (file, "\n");
  dump_function_inlining_decisions_1 (file, node, 1);
  fprintf (file, "\n");
}

/* Dump inlining decisions for all callsites in all functions to FILE.  */

static void
dump_cgraph_inlining_decisions (FILE *file)
{
  struct cgraph_node *node;

  fprintf (file, "\nInlining decisions:\n");
  for (node = cgraph_nodes; node; node = node->next)
    dump_function_inlining_decisions (file, node);
  fprintf (file, "\n");
}

/* Decide on the inlining.  We do so in the topological order to avoid
   expenses on updating data structures.  */

static unsigned int
cgraph_decide_inlining (void)
{
  struct cgraph_node *node;
  int nnodes;
  struct cgraph_node **order;
  int old_insns = 0;
  int i;
  int initial_insns = 0;
  bool redo_always_inline = true;
  struct inline_plan_file* plan_file;

  cgraph_remove_function_insertion_hook (function_insertion_hook_holder);

  max_count = 0;
  for (node = cgraph_nodes; node; node = node->next)
    if (node->analyzed && (node->needed || node->reachable))
      {
	struct cgraph_edge *e;

	initial_insns += inline_summary (node)->self_insns;
	gcc_assert (inline_summary (node)->self_insns == node->global.insns);
	for (e = node->callees; e; e = e->next_callee)
	  if (max_count < e->count)
	    max_count = e->count;
      }
  overall_insns = initial_insns;
  gcc_assert (!max_count || profile_info_available_p ());

  if (dump_file)
    {
      fprintf (dump_file, "cgraph_decide_inlining ()\n");
      fprintf (dump_file,
               "\nDeciding on inlining.  Starting with %i insns.\n",
               initial_insns);
      if (profile_info_available_p ())
	{
	  fprintf (dump_file, "maximum count = "
		   HOST_WIDEST_INT_PRINT_DEC "\n",
		   max_count);
	  fprintf (dump_file, "global maximum count = "
		   HOST_WIDEST_INT_PRINT_DEC "\n",
		   profile_info->sum_max);
	}
      fprintf (dump_file, "flag_inline_functions = %d\n",
               flag_inline_functions);
      fprintf (dump_file, "flag_guess_branch_prob = %d\n",
               flag_guess_branch_prob);
      fprintf (dump_file, "flag_branch_probabilities = %d\n",
               flag_branch_probabilities);
      fprintf (dump_file, "flag_sample_profile = %d\n", flag_sample_profile);
    }

  plan_file = get_plan_file_for_pass (current_pass);
  if (plan_file)
    {
      struct inline_plan *plan = read_inline_plan (plan_file->filename);
      plan->file = plan_file;
      apply_plan (plan, NULL);
      free_inline_plan (plan);
      goto end;
    }

  order = XCNEWVEC (struct cgraph_node *, cgraph_n_nodes);
  if (flag_limit_hot_components)
    compute_hot_components ();

  nnodes = cgraph_postorder (order);

  for (node = cgraph_nodes; node; node = node->next)
    node->aux = 0;

  if (dump_file)
    fprintf (dump_file, "\nInlining always_inline functions:\n");

  /* In the first pass mark all always_inline edges.  Do this with a priority
     so none of our later choices will make this impossible.  */
  while (redo_always_inline)
    {
      redo_always_inline = false;
      for (i = nnodes - 1; i >= 0; i--)
	{
	  struct cgraph_edge *e, *next;

	  node = order[i];

	  /* Handle nodes to be flattened, but don't update overall unit
	     size.  */
	  if (lookup_attribute ("flatten",
				DECL_ATTRIBUTES (node->decl)) != NULL)
	    {
	      if (dump_file)
		fprintf (dump_file,
			 "Flattening %s\n", cgraph_node_name (node));
	      cgraph_decide_inlining_incrementally (node, INLINE_ALL, 0);
	    }

	  if (!node->local.disregard_inline_limits)
	    continue;
	  if (dump_file)
	    fprintf (dump_file,
		     "\nConsidering %s %i insns (always inline)\n",
		     cgraph_node_name (node), node->global.insns);
	  old_insns = overall_insns;
	  for (e = node->callers; e; e = next)
	    {
	      next = e->next_caller;
	      if (!e->inline_failed
		  || gimple_call_cannot_inline_p (e->call_stmt))
		continue;
	      if (cgraph_recursive_inlining_p (e->caller, e->callee,
					       &e->inline_failed))
		continue;
	      if (!tree_can_inline_p (e->caller->decl, e->callee->decl))
		{
		  gimple_call_set_cannot_inline (e->call_stmt, true);
		  continue;
		}
              if (!dbg_cnt (inl))
                continue;

	      if (cgraph_mark_inline_edge (e, true, NULL))
		redo_always_inline = true;
	      if (dump_file)
		fprintf (dump_file,
			 "INFO: %s Inlined into %s which now has %i insns.\n",
			 cgraph_node_name (e->callee),
			 cgraph_node_name (e->caller),
			 e->caller->global.insns);
	    }
	  /* Inlining self recursive function might introduce new calls to
	     themselves we didn't see in the loop above.  Fill in the proper
	     reason why inline failed.  */
	  for (e = node->callers; e; e = e->next_caller)
	    if (e->inline_failed)
	      e->inline_failed = N_("recursive inlining");
	  if (dump_file)
	    fprintf (dump_file, 
		     " Inlined for a net change of %+i insns.\n",
		     overall_insns - old_insns);
	}
    }

  cgraph_decide_inlining_of_small_functions ();

  if (flag_inline_functions_called_once)
    {
      if (dump_file)
	fprintf (dump_file, "\nDeciding on functions called once:\n");

      /* And finally decide what functions are called once.  */
      for (i = nnodes - 1; i >= 0; i--)
	{
	  node = order[i];

	  if (node->callers
	      && !node->callers->next_caller
	      && !node->needed
	      && node->local.inlinable
	      && node->callers->inline_failed
	      && !gimple_call_cannot_inline_p (node->callers->call_stmt)
	      && !DECL_EXTERNAL (node->decl)
	      && !DECL_COMDAT (node->decl))
	    {
	      if (dump_file)
		{
		  fprintf (dump_file,
			   "\nConsidering %s %i insns.\n",
			   cgraph_node_name (node), node->global.insns);
		  fprintf (dump_file,
			   " Called once from %s %i insns.\n",
			   cgraph_node_name (node->callers->caller),
			   node->callers->caller->global.insns);
		}

	      old_insns = overall_insns;

	      if (cgraph_check_inline_constraints (node->callers->caller, node,
						   NULL, false)
                  && dbg_cnt (inl))
		{
		  cgraph_mark_inline (node->callers);
		  if (dump_file)
		    fprintf (dump_file,
			     "INFO: %s Inlined into %s which now has %i insns"
			     " for a net change of %+i insns.\n",
			     cgraph_node_name (node),
			     cgraph_node_name (node->callers->caller),
			     node->callers->caller->global.insns,
			     overall_insns - old_insns);
		}
	      else
		{
		  if (dump_file)
		    fprintf (dump_file,
			     " Inline limit reached, not inlined.\n");
		}
	    }
	}
    }
  free (order);
  if (flag_limit_hot_components)
    free_hot_components ();

 end:
  /* Free ipa-prop structures if they are no longer needed.  */
  if (flag_indirect_inlining)
    free_all_ipa_structures_after_iinln ();

  if (dump_file)
    fprintf (dump_file,
	     "\nInlined %i calls, eliminated %i functions, "
	     "%i insns turned to %i insns.\n\n",
	     ncalls_inlined, nfunctions_inlined, initial_insns,
	     overall_insns);

  if (dump_file && (dump_flags & TDF_DETAILS))
    dump_cgraph_inlining_decisions (dump_file);

  return 0;
}

/* Try to inline edge E from incremental inliner.  MODE specifies mode
   of inliner.

   We are detecting cycles by storing mode of inliner into cgraph_node last
   time we visited it in the recursion.  In general when mode is set, we have
   recursive inlining, but as an special case, we want to try harder inline
   ALWAYS_INLINE functions: consider callgraph a->b->c->b, with a being
   flatten, b being always inline.  Flattening 'a' will collapse
   a->b->c before hitting cycle.  To accommodate always inline, we however
   need to inline a->b->c->b.

   So after hitting cycle first time, we switch into ALWAYS_INLINE mode and
   stop inlining only after hitting ALWAYS_INLINE in ALWAY_INLINE mode.  */
static bool
try_inline (struct cgraph_edge *e, enum inlining_mode mode, int depth)
{
  struct cgraph_node *callee = e->callee;
  enum inlining_mode callee_mode = (enum inlining_mode) (size_t) callee->aux;
  bool always_inline = e->callee->local.disregard_inline_limits;

  /* We've hit cycle?  */
  if (callee_mode)
    {
      /* It is first time we see it and we are not in ALWAY_INLINE only
	 mode yet.  and the function in question is always_inline.  */
      if (always_inline && mode != INLINE_ALWAYS_INLINE)
	{
	  if (dump_file)
	    {
	      indent_to (dump_file, depth);
	      fprintf (dump_file,
		       "Hit cycle in %s, switching to always inline only.\n",
		       cgraph_node_name (callee));
	    }
	  mode = INLINE_ALWAYS_INLINE;
	}
      /* Otherwise it is time to give up.  */
      else
	{
	  if (dump_file)
	    {
	      indent_to (dump_file, depth);
	      fprintf (dump_file,
		       "Not inlining %s into %s to avoid cycle.\n",
		       cgraph_node_name (callee),
		       cgraph_node_name (e->caller));
	    }
	  e->inline_failed = (e->callee->local.disregard_inline_limits
		              ? N_("recursive inlining") : "");
          return false;
	}
    }
      
  callee->aux = (void *)(size_t) mode;
  if (dump_file)
    {
      indent_to (dump_file, depth);
      fprintf (dump_file, " Inlining %s into %s.\n",
	       cgraph_node_name (e->callee),
	       cgraph_node_name (e->caller));
    }
  if (e->inline_failed && dbg_cnt (inl))
    {
      cgraph_mark_inline (e);

      /* In order to fully inline always_inline functions, we need to
	 recurse here, since the inlined functions might not be processed by
	 incremental inlining at all yet.  

	 Also flattening needs to be done recursively.  */

      if (mode == INLINE_ALL || always_inline)
	cgraph_decide_inlining_incrementally (e->callee, mode, depth + 1);
    }
  callee->aux = (void *)(size_t) callee_mode;
  return true;
}

/* Decide on the inlining.  We do so in the topological order to avoid
   expenses on updating data structures.  
   DEPTH is depth of recursion, used only for debug output.  */

static bool
cgraph_decide_inlining_incrementally (struct cgraph_node *node,
				      enum inlining_mode mode,
				      int depth)
{
  struct cgraph_edge *e;
  bool inlined = false;
  const char *failed_reason;
  enum inlining_mode old_mode;
  bool after_tree_profile =
    (DECL_STRUCT_FUNCTION (node->decl))->after_tree_profile;

#ifdef ENABLE_CHECKING
  verify_cgraph_node (node);
#endif

  if (dump_file)
    {
      indent_to (dump_file, depth);
      fprintf (dump_file,
	       "cgraph_decide_inlining_incrementally (%s/%d, %s, %d)\n",
	       cgraph_node_name (node), node->uid,
	       inlining_mode_strings[mode], depth);
    }
  old_mode = (enum inlining_mode) (size_t)node->aux;

  if (mode != INLINE_ALWAYS_INLINE
      && lookup_attribute ("flatten", DECL_ATTRIBUTES (node->decl)) != NULL)
    {
      if (dump_file)
	{
	  indent_to (dump_file, depth);
	  fprintf (dump_file, "Flattening %s\n", cgraph_node_name (node));
	}
      mode = INLINE_ALL;
    }

  node->aux = (void *)(size_t) mode;

  /* First of all look for always inline functions.  */
  for (e = node->callees; e; e = e->next_callee)
    {
      if (cgraph_is_fake_indirect_call_edge (e))
        continue;

      if (!e->callee->local.disregard_inline_limits
	  && (mode != INLINE_ALL || !e->callee->local.inlinable))
	continue;
      if (gimple_call_cannot_inline_p (e->call_stmt))
	continue;
      /* Don't do cross-module inlining before profile-use, so that we have a
	 consistent CFG between the profile-gen and profile-use passes.  */
      if (!after_tree_profile
	  && L_IPO_COMP_MODE
          && !cgraph_is_inline_body_available_in_module (
              e->callee->decl, cgraph_get_module_id (e->caller->decl)))
	{
          e->inline_failed = N_("inter-module inlining disabled");
          if (dump_file)
            {
              indent_to (dump_file, depth);
              fprintf (dump_file, "Not considering inlining %s: %s.\n",
                       cgraph_node_name (e->callee), e->inline_failed);
            }
          continue;
	}
      /* When the edge is already inlined, we just need to recurse into
	 it in order to fully flatten the leaves.  */
      if (!e->inline_failed && mode == INLINE_ALL)
	{
          inlined |= try_inline (e, mode, depth);
	  continue;
	}
      if (dump_file)
	{
	  indent_to (dump_file, depth);
	  fprintf (dump_file,
		   "Considering to always inline inline candidate %s/%d.\n",
		   cgraph_node_name (e->callee), e->callee->uid);
	}
      if (cgraph_recursive_inlining_p (node, e->callee, &e->inline_failed))
	{
	  if (dump_file)
	    {
	      indent_to (dump_file, depth);
	      fprintf (dump_file, "Not inlining: recursive call.\n");
	    }
	  continue;
	}
      if (!tree_can_inline_p (node->decl, e->callee->decl))
	{
	  gimple_call_set_cannot_inline (e->call_stmt, true);
	  if (dump_file)
	    {
	      indent_to (dump_file, depth);
	      fprintf (dump_file,
		       "Not inlining: Target specific option mismatch.\n");
	    }
	  continue;
	}
      if (gimple_in_ssa_p (DECL_STRUCT_FUNCTION (node->decl))
	  != gimple_in_ssa_p (DECL_STRUCT_FUNCTION (e->callee->decl)))
	{
	  if (dump_file)
	    {
	      indent_to (dump_file, depth);
	      fprintf (dump_file, "Not inlining: SSA form does not match.\n");
	    }
	  continue;
	}
      if (!e->callee->analyzed && !e->callee->inline_decl)
	{
	  if (dump_file)
	    {
	      indent_to (dump_file, depth);
	      fprintf (dump_file,
		       "Not inlining: Function body no longer available.\n");
	    }
	  continue;
	}
      inlined |= try_inline (e, mode, depth);
    }

  /* Now do the automatic inlining.  */
  if (mode != INLINE_ALL && mode != INLINE_ALWAYS_INLINE)
    for (e = node->callees; e; e = e->next_callee)
      {
        if (cgraph_is_fake_indirect_call_edge (e))
          continue;
	if (!e->callee->local.inlinable
	    || !e->inline_failed
	    || e->callee->local.disregard_inline_limits)
	  continue;
	/* Don't do cross-module inlining before profile-use, so that we have a
	   consistent CFG between the profile-gen and profile-use passes.  */
	if (!after_tree_profile
            && L_IPO_COMP_MODE
            && !cgraph_is_inline_body_available_in_module (
                e->callee->decl, cgraph_get_module_id (e->caller->decl)))
	  {
            e->inline_failed = N_("inter-module inlining disabled");
            if (dump_file)
              {
                indent_to (dump_file, depth);
                fprintf (dump_file, "Not inlining considering inlining %s: %s\n", 
                         cgraph_node_name (e->callee), e->inline_failed);
              }
            continue;
	  }
	if (dump_file)
	  fprintf (dump_file, "Considering inline candidate %s/%d.\n",
		   cgraph_node_name (e->callee), e->callee->uid);
	if (cgraph_recursive_inlining_p (node, e->callee, &e->inline_failed))
	  {
	    if (dump_file)
	      {
		indent_to (dump_file, depth);
		fprintf (dump_file, "Not inlining: recursive call.\n");
	      }
	    continue;
	  }
	if (gimple_in_ssa_p (DECL_STRUCT_FUNCTION (node->decl))
	    != gimple_in_ssa_p (DECL_STRUCT_FUNCTION (e->callee->decl)))
	  {
	    if (dump_file)
	      {
		indent_to (dump_file, depth);
		fprintf (dump_file, "Not inlining: SSA form does not match.\n");
	      }
	    continue;
	  }
	/* When the function body would grow and inlining the function won't
	   eliminate the need for offline copy of the function, don't inline.
	 */
	if ((mode == INLINE_SIZE
	     || (!flag_inline_functions
		 && !DECL_DECLARED_INLINE_P (e->callee->decl)))
	    && (cgraph_estimate_size_after_inlining (1, e->caller, e->callee)
		> e->caller->global.insns)
	    && (cgraph_estimate_growth (e->callee) > 0
                /* With lightweight IPO, due to static function promtion,
                   it is hard to enable this heuristic and maintain consistent
                   pre-profiling inline decisions between profiile generate
                   and profile use passes.  */
                || (!after_tree_profile && flag_dyn_ipa)))
	  {
	    if (dump_file)
	      {
		indent_to (dump_file, depth);
		fprintf (dump_file,
			 "Not inlining: code size would grow by %i insns.\n",
			 cgraph_estimate_size_after_inlining (1, e->caller,
							      e->callee)
			 - e->caller->global.insns);
	      }
	    continue;
	  }
	if (!cgraph_check_inline_constraints (node, e->callee, &e->inline_failed,
					      false)
	    || gimple_call_cannot_inline_p (e->call_stmt))
	  {
	    if (dump_file)
	      {
		indent_to (dump_file, depth);
		fprintf (dump_file, "Not inlining: %s.\n", e->inline_failed);
	      }
	    continue;
	  }
	if (!e->callee->analyzed && !e->callee->inline_decl)
	  {
	    if (dump_file)
	      {
		indent_to (dump_file, depth);
		fprintf (dump_file,
			 "Not inlining: Function body no longer available.\n");
	      }
	    continue;
	  }
	if (!tree_can_inline_p (node->decl, e->callee->decl))
	  {
	    gimple_call_set_cannot_inline (e->call_stmt, true);
	    if (dump_file)
	      {
		indent_to (dump_file, depth);
		fprintf (dump_file,
			 "Not inlining: Target specific option mismatch.\n");
	      }
	    continue;
	  }
	if (cgraph_default_inline_p (e->callee, &failed_reason))
	  {
	    bool success = try_inline (e, mode, depth);
	    if (dump_file && !success)
	      fprintf (dump_file, "Not inlining: %s\n", failed_reason);
	    inlined |= success;
	  }
        else
          {
	    if (dump_file)
	      {
		indent_to (dump_file, depth);
		fprintf (dump_file,
			 "Not inlining: %s .\n", failed_reason);
              }
          }
      }
  node->aux = (void *)(size_t) old_mode;
  return inlined;
}

/* Because inlining might remove no-longer reachable nodes, we need to
   keep the array visible to garbage collector to avoid reading collected
   out nodes.  */
static int nnodes;
static GTY ((length ("nnodes"))) struct cgraph_node **order;

/* Do inlining of small functions.  Doing so early helps profiling and other
   passes to be somewhat more effective and avoids some code duplication in
   later real inlining pass for testcases with very many function calls.  */
static unsigned int
cgraph_early_inlining (void)
{
  struct cgraph_node *node = cgraph_node (current_function_decl);
  unsigned int todo = 0;
  bool inlined;

  if (sorrycount || errorcount)
    return 0;

  if (inline_plan_files)
    {
      struct inline_plan_file *pfile = get_plan_file_for_pass (current_pass);

      /* If early inlining plan exists and is for previous inlining
         pass, then free it.  */
      if (einline_plan && einline_plan->file != pfile)
        {
          free_inline_plan (einline_plan);
          einline_plan = NULL;
        }

      /* Read in new plan for this pass, if it exists and has not been
         read in yet.  */
      if (pfile && einline_plan == NULL)
        {
          einline_plan = read_inline_plan (pfile->filename);
          einline_plan->file = pfile;
        }
    }

  if (einline_plan)
    inlined = apply_plan (einline_plan, node);
  else
    inlined = cgraph_decide_inlining_incrementally (node, INLINE_SIZE, 0);

  if (inlined)
    {
      timevar_push (TV_INTEGRATION);
      todo = optimize_inline_calls (current_function_decl);
      timevar_pop (TV_INTEGRATION);
    }
  cfun->always_inline_functions_inlined = true;
  return todo;
}

/* When inlining shall be performed.  */
static bool
cgraph_gate_early_inlining (void)
{
  return flag_early_inlining;
}

struct gimple_opt_pass pass_early_inline = 
{
 {
  GIMPLE_PASS,
  "einline",	 			/* name */
  cgraph_gate_early_inlining,		/* gate */
  cgraph_early_inlining,		/* execute */
  NULL,					/* sub */
  NULL,					/* next */
  0,					/* static_pass_number */
  TV_INLINE_HEURISTICS,			/* tv_id */
  0,	                                /* properties_required */
  PROP_cfg,				/* properties_provided */
  0,					/* properties_destroyed */
  0,					/* todo_flags_start */
  TODO_dump_func    			/* todo_flags_finish */
 }
};

/* When inlining shall be performed.  */
bool
cgraph_gate_ipa_early_inlining (void)
{
  if (flag_early_inlining)
    {
      if (flag_branch_probabilities || flag_test_coverage
	  || flag_sample_profile || profile_arc_flag)
	return true;
      else if (inline_plan_files)
	{
	  /* If there is a inline plan specified for this early inlining
	     pass, then the pass should be run.  The actual early inlining
	     pass is a subpass of PASS_IPA_EARLY_INLINE, so walk the
	     subpasses to see if there exists a plan.  */
	  struct opt_pass *pass;
	  for (pass = current_pass->sub; pass; pass = pass->next)
	    if (get_plan_file_for_pass (pass))
	      return true;
	}
    }
  return false;
}

/* IPA pass wrapper for early inlining pass.  We need to run early inlining
   before tree profiling so we have stand alone IPA pass for doing so.  */
struct simple_ipa_opt_pass pass_ipa_early_inline = 
{
 {
  SIMPLE_IPA_PASS,
  "einline_ipa",			/* name */
  cgraph_gate_ipa_early_inlining,	/* gate */
  NULL,					/* execute */
  NULL,					/* sub */
  NULL,					/* next */
  0,					/* static_pass_number */
  TV_INLINE_HEURISTICS,			/* tv_id */
  0,	                                /* properties_required */
  PROP_cfg,				/* properties_provided */
  0,					/* properties_destroyed */
  0,					/* todo_flags_start */
  TODO_dump_cgraph 		        /* todo_flags_finish */
 }
};

/* Compute parameters of functions used by inliner.  */
unsigned int
compute_inline_parameters (struct cgraph_node *node)
{
  HOST_WIDE_INT self_stack_size;
  int hot_self_insns = 0;

  gcc_assert (!node->global.inlined_to);

  /* Estimate the stack size for the function.  But not at -O0
     because estimated_stack_frame_size is a quadratic problem.  */
  self_stack_size = optimize ? estimated_stack_frame_size () : 0;
  inline_summary (node)->estimated_self_stack_size = self_stack_size;
  node->global.estimated_stack_size = self_stack_size;
  node->global.estimated_stack_size_pessimistic = self_stack_size;
  node->global.stack_frame_offset = 0;

  /* Can this function be inlined at all?  */
  node->local.inlinable = tree_inlinable_function_p (node->decl);

  /* Estimate the number of instructions for this function.
     ??? At -O0 we don't use this information except for the dumps, and
	 even then only for always_inline functions.  But disabling this
	 causes ICEs in the inline heuristics...  */
  inline_summary (node)->self_insns
      = estimate_num_insns_fn (node->decl, &eni_inlining_weights,
                               &hot_self_insns);
  inline_summary (node)->self_hot_insns = hot_self_insns;
  if (node->local.inlinable && !node->local.disregard_inline_limits)
    node->local.disregard_inline_limits
        = DECL_DISREGARD_INLINE_LIMITS (node->decl);

  /* Inlining characteristics are maintained by the cgraph_mark_inline.  */
  node->global.insns = inline_summary (node)->self_insns;
  return 0;
}


/* Compute parameters of functions used by inliner using
   current_function_decl.  */
static unsigned int
compute_inline_parameters_for_current (void)
{
  compute_inline_parameters (cgraph_node (current_function_decl));
  return 0;
}

struct gimple_opt_pass pass_inline_parameters = 
{
 {
  GIMPLE_PASS,
  NULL,	 				/* name */
  NULL,					/* gate */
  compute_inline_parameters_for_current,/* execute */
  NULL,					/* sub */
  NULL,					/* next */
  0,					/* static_pass_number */
  TV_INLINE_HEURISTICS,			/* tv_id */
  0,	                                /* properties_required */
  PROP_cfg,				/* properties_provided */
  0,					/* properties_destroyed */
  0,					/* todo_flags_start */
  0					/* todo_flags_finish */
 }
};

/* This function performs intraprocedural analyzis in NODE that is required to
   inline indirect calls.  */
static void
inline_indirect_intraprocedural_analysis (struct cgraph_node *node)
{
  struct cgraph_edge *cs;

  if (!flag_ipa_cp)
    {
      ipa_initialize_node_params (node);
      ipa_detect_param_modifications (node);
    }
  ipa_analyze_params_uses (node);

  if (!flag_ipa_cp)
    for (cs = node->callees; cs; cs = cs->next_callee)
      {
	ipa_count_arguments (cs);
	ipa_compute_jump_functions (cs);
      }

  if (dump_file)
    {
      ipa_print_node_params (dump_file, node);
      ipa_print_node_jump_functions (dump_file, node);
    }
}

/* Note function body size.  */
static void
analyze_function (struct cgraph_node *node)
{
  push_cfun (DECL_STRUCT_FUNCTION (node->decl));
  current_function_decl = node->decl;

  compute_inline_parameters (node);
  if (flag_indirect_inlining)
    inline_indirect_intraprocedural_analysis (node);

  current_function_decl = NULL;
  pop_cfun ();
}

/* Called when new function is inserted to callgraph late.  */
static void
add_new_function (struct cgraph_node *node, void *data ATTRIBUTE_UNUSED)
{
  analyze_function (node);
}

/* Note function body size.  */
static void
inline_generate_summary (void)
{
  struct cgraph_node *node;

  function_insertion_hook_holder =
      cgraph_add_function_insertion_hook (&add_new_function, NULL);

  if (flag_indirect_inlining)
    {
      ipa_register_cgraph_hooks ();
      ipa_check_create_node_params ();
      ipa_check_create_edge_args ();
    }

  for (node = cgraph_nodes; node; node = node->next)
    if (node->analyzed)
      analyze_function (node);
  
  return;
}

/* Apply inline plan to function.  */
static unsigned int
inline_transform (struct cgraph_node *node)
{
  unsigned int todo = 0;
  struct cgraph_edge *e;

  /* We might need the body of this function so that we can expand
     it inline somewhere else.  */
  if (cgraph_preserve_function_body_p (node->decl))
    save_inline_function_body (node);

  for (e = node->callees; e; e = e->next_callee)
    if (!e->inline_failed || warn_inline)
      break;

  if (e)
    {
      timevar_push (TV_INTEGRATION);
      todo = optimize_inline_calls (current_function_decl);
      timevar_pop (TV_INTEGRATION);
    }
  return todo | execute_fixup_cfg ();
}

struct ipa_opt_pass pass_ipa_inline = 
{
 {
  IPA_PASS,
  "inline",				/* name */
  NULL,					/* gate */
  cgraph_decide_inlining,		/* execute */
  NULL,					/* sub */
  NULL,					/* next */
  0,					/* static_pass_number */
  TV_INLINE_HEURISTICS,			/* tv_id */
  0,	                                /* properties_required */
  PROP_cfg,				/* properties_provided */
  0,					/* properties_destroyed */
  TODO_remove_functions,		/* todo_flags_finish */
  TODO_dump_cgraph | TODO_dump_func
  | TODO_remove_functions		/* todo_flags_finish */
 },
 inline_generate_summary,		/* generate_summary */
 NULL,					/* write_summary */
 NULL,					/* read_summary */
 NULL,					/* function_read_summary */
 0,					/* TODOs */
 inline_transform,			/* function_transform */
 NULL,					/* variable_transform */
};


#include "gt-ipa-inline.h"
