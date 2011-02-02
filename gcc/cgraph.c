/* Callgraph handling code.
   Copyright (C) 2003, 2004, 2005, 2006, 2007, 2008
   Free Software Foundation, Inc.
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

/*  This file contains basic routines manipulating call graph

The callgraph:

    The call-graph is data structure designed for intra-procedural optimization
    but it is also used in non-unit-at-a-time compilation to allow easier code
    sharing.

    The call-graph consist of nodes and edges represented via linked lists.
    Each function (external or not) corresponds to the unique node.

    The mapping from declarations to call-graph nodes is done using hash table
    based on DECL_UID.  The call-graph nodes are created lazily using
    cgraph_node function when called for unknown declaration.

    The callgraph at the moment does not represent indirect calls or calls
    from other compilation unit.  Flag NEEDED is set for each node that may
    be accessed in such an invisible way and it shall be considered an
    entry point to the callgraph.

    Interprocedural information:

      Callgraph is place to store data needed for interprocedural optimization.
      All data structures are divided into three components: local_info that
      is produced while analyzing the function, global_info that is result
      of global walking of the callgraph on the end of compilation and
      rtl_info used by RTL backend to propagate data from already compiled
      functions to their callers.

    Inlining plans:

      The function inlining information is decided in advance and maintained
      in the callgraph as so called inline plan.
      For each inlined call, the callee's node is cloned to represent the
      new function copy produced by inliner.
      Each inlined call gets a unique corresponding clone node of the callee
      and the data structure is updated while inlining is performed, so
      the clones are eliminated and their callee edges redirected to the
      caller.

      Each edge has "inline_failed" field.  When the field is set to NULL,
      the call will be inlined.  When it is non-NULL it contains a reason
      why inlining wasn't performed.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "tree.h"
#include "tree-inline.h"
#include "langhooks.h"
#include "hashtab.h"
#include "toplev.h"
#include "flags.h"
#include "ggc.h"
#include "debug.h"
#include "target.h"
#include "basic-block.h"
#include "cgraph.h"
#include "varray.h"
#include "output.h"
#include "intl.h"
#include "gimple.h"
#include "tree-dump.h"
#include "tree-flow.h"
#include "value-prof.h"
#include "params.h"

static void cgraph_node_remove_callers (struct cgraph_node *node);
static inline void cgraph_edge_remove_caller (struct cgraph_edge *e);
static inline void cgraph_edge_remove_callee (struct cgraph_edge *e);

/* Hash table used to convert declarations into nodes.  */
static GTY((param_is (struct cgraph_node))) htab_t cgraph_hash;
/* Hash table used to convert assembler names into nodes.  */
static GTY((param_is (struct cgraph_node))) htab_t assembler_name_hash;

/* The linked list of cgraph nodes.  */
struct cgraph_node *cgraph_nodes;

/* Queue of cgraph nodes scheduled to be lowered.  */
struct cgraph_node *cgraph_nodes_queue;

/* Queue of cgraph nodes scheduled to be added into cgraph.  This is a
   secondary queue used during optimization to accommodate passes that
   may generate new functions that need to be optimized and expanded.  */
struct cgraph_node *cgraph_new_nodes;

/* Number of nodes in existence.  */
int cgraph_n_nodes;

/* Maximal uid used in cgraph nodes.  */
int cgraph_max_uid;

/* Maximal uid used in cgraph edges.  */
int cgraph_edge_max_uid;

/* Maximal pid used for profiling */
int cgraph_max_pid;

/* Set when whole unit has been analyzed so we can access global info.  */
bool cgraph_global_info_ready = false;

/* What state callgraph is in right now.  */
enum cgraph_state cgraph_state = CGRAPH_STATE_CONSTRUCTION;

/* Set when the cgraph is fully build and the basic flags are computed.  */
bool cgraph_function_flags_ready = false;

/* Linked list of cgraph asm nodes.  */
struct cgraph_asm_node *cgraph_asm_nodes;

/* Last node in cgraph_asm_nodes.  */
static GTY(()) struct cgraph_asm_node *cgraph_asm_last_node;

/* The order index of the next cgraph node to be created.  This is
   used so that we can sort the cgraph nodes in order by when we saw
   them, to support -fno-toplevel-reorder.  */
int cgraph_order;

/* List of hooks trigerred on cgraph_edge events.  */
struct cgraph_edge_hook_list {
  cgraph_edge_hook hook;
  void *data;
  struct cgraph_edge_hook_list *next;
};

/* List of hooks trigerred on cgraph_node events.  */
struct cgraph_node_hook_list {
  cgraph_node_hook hook;
  void *data;
  struct cgraph_node_hook_list *next;
};

/* List of hooks trigerred on events involving two cgraph_edges.  */
struct cgraph_2edge_hook_list {
  cgraph_2edge_hook hook;
  void *data;
  struct cgraph_2edge_hook_list *next;
};

/* List of hooks trigerred on events involving two cgraph_nodes.  */
struct cgraph_2node_hook_list {
  cgraph_2node_hook hook;
  void *data;
  struct cgraph_2node_hook_list *next;
};

/* List of hooks triggered when an edge is removed.  */
struct cgraph_edge_hook_list *first_cgraph_edge_removal_hook;
/* List of hooks triggered when a node is removed.  */
struct cgraph_node_hook_list *first_cgraph_node_removal_hook;
/* List of hooks triggered when an edge is duplicated.  */
struct cgraph_2edge_hook_list *first_cgraph_edge_duplicated_hook;
/* List of hooks triggered when a node is duplicated.  */
struct cgraph_2node_hook_list *first_cgraph_node_duplicated_hook;
/* List of hooks triggered when an function is inserted.  */
struct cgraph_node_hook_list *first_cgraph_function_insertion_hook;

/* Head of a linked list of unused (freed) call graph nodes.
   Do not GTY((delete)) this list so UIDs gets reliably recycled.  */
static GTY(()) struct cgraph_node *free_nodes;
/* Head of a linked list of unused (freed) call graph edges.
   Do not GTY((delete)) this list so UIDs gets reliably recycled.  */
static GTY(()) struct cgraph_edge *free_edges;

/* Macros to access the next item in the list of free cgraph nodes and
   edges. */
#define NEXT_FREE_NODE(NODE) (NODE)->next
#define NEXT_FREE_EDGE(EDGE) (EDGE)->prev_caller

/* Register HOOK to be called with DATA on each removed edge.  */
struct cgraph_edge_hook_list *
cgraph_add_edge_removal_hook (cgraph_edge_hook hook, void *data)
{
  struct cgraph_edge_hook_list *entry;
  struct cgraph_edge_hook_list **ptr = &first_cgraph_edge_removal_hook;

  entry = (struct cgraph_edge_hook_list *) xmalloc (sizeof (*entry));
  entry->hook = hook;
  entry->data = data;
  entry->next = NULL;
  while (*ptr)
    ptr = &(*ptr)->next;
  *ptr = entry;
  return entry;
}

/* Remove ENTRY from the list of hooks called on removing edges.  */
void
cgraph_remove_edge_removal_hook (struct cgraph_edge_hook_list *entry)
{
  struct cgraph_edge_hook_list **ptr = &first_cgraph_edge_removal_hook;

  while (*ptr != entry)
    ptr = &(*ptr)->next;
  *ptr = entry->next;
  free (entry);
}

/* Call all edge removal hooks.  */
static void
cgraph_call_edge_removal_hooks (struct cgraph_edge *e)
{
  struct cgraph_edge_hook_list *entry = first_cgraph_edge_removal_hook;
  while (entry)
  {
    entry->hook (e, entry->data);
    entry = entry->next;
  }
}

/* Register HOOK to be called with DATA on each removed node.  */
struct cgraph_node_hook_list *
cgraph_add_node_removal_hook (cgraph_node_hook hook, void *data)
{
  struct cgraph_node_hook_list *entry;
  struct cgraph_node_hook_list **ptr = &first_cgraph_node_removal_hook;

  entry = (struct cgraph_node_hook_list *) xmalloc (sizeof (*entry));
  entry->hook = hook;
  entry->data = data;
  entry->next = NULL;
  while (*ptr)
    ptr = &(*ptr)->next;
  *ptr = entry;
  return entry;
}

/* Remove ENTRY from the list of hooks called on removing nodes.  */
void
cgraph_remove_node_removal_hook (struct cgraph_node_hook_list *entry)
{
  struct cgraph_node_hook_list **ptr = &first_cgraph_node_removal_hook;

  while (*ptr != entry)
    ptr = &(*ptr)->next;
  *ptr = entry->next;
  free (entry);
}

/* Call all node removal hooks.  */
static void
cgraph_call_node_removal_hooks (struct cgraph_node *node)
{
  struct cgraph_node_hook_list *entry = first_cgraph_node_removal_hook;
  while (entry)
  {
    entry->hook (node, entry->data);
    entry = entry->next;
  }
}

/* Register HOOK to be called with DATA on each removed node.  */
struct cgraph_node_hook_list *
cgraph_add_function_insertion_hook (cgraph_node_hook hook, void *data)
{
  struct cgraph_node_hook_list *entry;
  struct cgraph_node_hook_list **ptr = &first_cgraph_function_insertion_hook;

  entry = (struct cgraph_node_hook_list *) xmalloc (sizeof (*entry));
  entry->hook = hook;
  entry->data = data;
  entry->next = NULL;
  while (*ptr)
    ptr = &(*ptr)->next;
  *ptr = entry;
  return entry;
}

/* Remove ENTRY from the list of hooks called on removing nodes.  */
void
cgraph_remove_function_insertion_hook (struct cgraph_node_hook_list *entry)
{
  struct cgraph_node_hook_list **ptr = &first_cgraph_function_insertion_hook;

  while (*ptr != entry)
    ptr = &(*ptr)->next;
  *ptr = entry->next;
  free (entry);
}

/* Call all node removal hooks.  */
void
cgraph_call_function_insertion_hooks (struct cgraph_node *node)
{
  struct cgraph_node_hook_list *entry = first_cgraph_function_insertion_hook;
  while (entry)
  {
    entry->hook (node, entry->data);
    entry = entry->next;
  }
}

/* Register HOOK to be called with DATA on each duplicated edge.  */
struct cgraph_2edge_hook_list *
cgraph_add_edge_duplication_hook (cgraph_2edge_hook hook, void *data)
{
  struct cgraph_2edge_hook_list *entry;
  struct cgraph_2edge_hook_list **ptr = &first_cgraph_edge_duplicated_hook;

  entry = (struct cgraph_2edge_hook_list *) xmalloc (sizeof (*entry));
  entry->hook = hook;
  entry->data = data;
  entry->next = NULL;
  while (*ptr)
    ptr = &(*ptr)->next;
  *ptr = entry;
  return entry;
}

/* Remove ENTRY from the list of hooks called on duplicating edges.  */
void
cgraph_remove_edge_duplication_hook (struct cgraph_2edge_hook_list *entry)
{
  struct cgraph_2edge_hook_list **ptr = &first_cgraph_edge_duplicated_hook;

  while (*ptr != entry)
    ptr = &(*ptr)->next;
  *ptr = entry->next;
  free (entry);
}

/* Call all edge duplication hooks.  */
static void
cgraph_call_edge_duplication_hooks (struct cgraph_edge *cs1,
				    struct cgraph_edge *cs2)
{
  struct cgraph_2edge_hook_list *entry = first_cgraph_edge_duplicated_hook;
  while (entry)
  {
    entry->hook (cs1, cs2, entry->data);
    entry = entry->next;
  }
}

/* Register HOOK to be called with DATA on each duplicated node.  */
struct cgraph_2node_hook_list *
cgraph_add_node_duplication_hook (cgraph_2node_hook hook, void *data)
{
  struct cgraph_2node_hook_list *entry;
  struct cgraph_2node_hook_list **ptr = &first_cgraph_node_duplicated_hook;

  entry = (struct cgraph_2node_hook_list *) xmalloc (sizeof (*entry));
  entry->hook = hook;
  entry->data = data;
  entry->next = NULL;
  while (*ptr)
    ptr = &(*ptr)->next;
  *ptr = entry;
  return entry;
}

/* Remove ENTRY from the list of hooks called on duplicating nodes.  */
void
cgraph_remove_node_duplication_hook (struct cgraph_2node_hook_list *entry)
{
  struct cgraph_2node_hook_list **ptr = &first_cgraph_node_duplicated_hook;

  while (*ptr != entry)
    ptr = &(*ptr)->next;
  *ptr = entry->next;
  free (entry);
}

/* Call all node duplication hooks.  */
static void
cgraph_call_node_duplication_hooks (struct cgraph_node *node1,
				    struct cgraph_node *node2)
{
  struct cgraph_2node_hook_list *entry = first_cgraph_node_duplicated_hook;
  while (entry)
  {
    entry->hook (node1, node2, entry->data);
    entry = entry->next;
  }
}

/* Returns a hash code for P.  */

static hashval_t
hash_node (const void *p)
{
  const struct cgraph_node *n = (const struct cgraph_node *) p;
  return (hashval_t) DECL_UID (n->decl);
}

/* Returns nonzero if P1 and P2 are equal.  */

static int
eq_node (const void *p1, const void *p2)
{
  const struct cgraph_node *n1 = (const struct cgraph_node *) p1;
  const struct cgraph_node *n2 = (const struct cgraph_node *) p2;
  return DECL_UID (n1->decl) == DECL_UID (n2->decl);
}

/* Allocate new callgraph node and insert it into basic data structures.  */

static struct cgraph_node *
cgraph_create_node (void)
{
  struct cgraph_node *node;

  if (free_nodes)
    {
      node = free_nodes;
      free_nodes = NEXT_FREE_NODE (node);
    }
  else
    {
      node = GGC_CNEW (struct cgraph_node);
      node->uid = cgraph_max_uid++;
    }

  node->next = cgraph_nodes;
  node->pid = -1;
  node->order = cgraph_order++;
  if (cgraph_nodes)
    cgraph_nodes->previous = node;
  node->previous = NULL;
  node->global.estimated_average_growth = INT_MIN;
  cgraph_nodes = node;
  cgraph_n_nodes++;
  return node;
}

/* Add an entry in assembler hash for NODE.  */
void
cgraph_add_assembler_hash_node (struct cgraph_node *node)
{
  if (assembler_name_hash)
    {
      void **aslot;
      tree name = DECL_ASSEMBLER_NAME (node->decl);

      aslot = htab_find_slot_with_hash (assembler_name_hash, name,
					decl_assembler_name_hash (name),
					INSERT);
      /* We can have multiple declarations with same assembler name. For C++
	 it is __builtin_strlen and strlen, for instance.  Do we need to
	 record them all?  Original implementation marked just first one
	 so lets hope for the best.  */
      if (*aslot == NULL)
	*aslot = node;
    }
}

/* Remove from assembler hash for NODE.  */
void
cgraph_remove_assembler_hash_node (struct cgraph_node *node)
{
  void **slot;
  if (assembler_name_hash)
    {
      tree name = DECL_ASSEMBLER_NAME (node->decl);
      slot = htab_find_slot_with_hash (assembler_name_hash, name,
				       decl_assembler_name_hash (name),
				       NO_INSERT);
      /* Inline clones are not hashed.  */
      if (slot && *slot == node)
        htab_clear_slot (assembler_name_hash, slot);
    }
}

/* Return cgraph node assigned to DECL.  Create new one when needed.  */

struct cgraph_node *
cgraph_node (tree decl)
{
  struct cgraph_node key, *node, **slot;

  gcc_assert (TREE_CODE (decl) == FUNCTION_DECL);

  if (!cgraph_hash)
    cgraph_hash = htab_create_ggc (10, hash_node, eq_node, NULL);

  key.decl = decl;

  slot = (struct cgraph_node **) htab_find_slot (cgraph_hash, &key, INSERT);

  if (*slot)
    {
      node = *slot;
      if (!node->master_clone)
	node->master_clone = node;
      return node;
    }

  node = cgraph_create_node ();
  node->decl = decl;
  *slot = node;
  if (DECL_CONTEXT (decl) && TREE_CODE (DECL_CONTEXT (decl)) == FUNCTION_DECL)
    {
      node->origin = cgraph_node (DECL_CONTEXT (decl));
      node->next_nested = node->origin->nested;
      node->origin->nested = node;
      node->master_clone = node;
    }
  cgraph_add_assembler_hash_node (node);
  return node;
}

/* Insert already constructed node into hashtable.  */

void
cgraph_insert_node_to_hashtable (struct cgraph_node *node)
{
  struct cgraph_node **slot;

  slot = (struct cgraph_node **) htab_find_slot (cgraph_hash, node, INSERT);

  gcc_assert (!*slot);
  *slot = node;
}

/* Returns a hash code for P.  */

static hashval_t
hash_node_by_assembler_name (const void *p)
{
  const struct cgraph_node *n = (const struct cgraph_node *) p;
  return (hashval_t) decl_assembler_name_hash (DECL_ASSEMBLER_NAME (n->decl));
}

/* Returns nonzero if P1 and P2 are equal.  */

static int
eq_assembler_name (const void *p1, const void *p2)
{
  const struct cgraph_node *n1 = (const struct cgraph_node *) p1;
  const_tree name = (const_tree)p2;
  return (decl_assembler_name_equal (n1->decl, name));
}

/* Return the cgraph node that has ASMNAME for its DECL_ASSEMBLER_NAME.
   Return NULL if there's no such node.  */

struct cgraph_node *
cgraph_node_for_asm (tree asmname)
{
  struct cgraph_node *node;
  void **slot;

  if (!assembler_name_hash)
    {
      assembler_name_hash =
	htab_create_ggc (10, hash_node_by_assembler_name, eq_assembler_name,
			 NULL);
      for (node = cgraph_nodes; node; node = node->next)
        if (!node->global.inlined_to)
	  {
	    tree name = DECL_ASSEMBLER_NAME (node->decl);
	    slot = htab_find_slot_with_hash (assembler_name_hash, name,
					     decl_assembler_name_hash (name),
					     INSERT);
	    /* We can have multiple declarations with same assembler name. For C++
	       it is __builtin_strlen and strlen, for instance.  Do we need to
	       record them all?  Original implementation marked just first one
	       so lets hope for the best.  */
	    if (*slot)
	      continue;
	    *slot = node;
	  }
    }

  slot = htab_find_slot_with_hash (assembler_name_hash, asmname,
				   decl_assembler_name_hash (asmname),
				   NO_INSERT);

  if (slot)
    return (struct cgraph_node *) *slot;
  return NULL;
}

/* Returns a hash value for X (which really is a die_struct).  */

static hashval_t
edge_hash (const void *x)
{
  return htab_hash_pointer (((const struct cgraph_edge *) x)->call_stmt);
}

/* Return nonzero if decl_id of die_struct X is the same as UID of decl *Y.  */

static int
edge_eq (const void *x, const void *y)
{
  return ((const struct cgraph_edge *) x)->call_stmt == y;
}


/* Return the callgraph edge representing the GIMPLE_CALL statement
   CALL_STMT.  */

struct cgraph_edge *
cgraph_edge (struct cgraph_node *node, gimple call_stmt)
{
  struct cgraph_edge *e, *e2;
  int n = 0;

  if (node->call_site_hash)
    return (struct cgraph_edge *)
      htab_find_with_hash (node->call_site_hash, call_stmt,
      	                   htab_hash_pointer (call_stmt));

  /* This loop may turn out to be performance problem.  In such case adding
     hashtables into call nodes with very many edges is probably best
     solution.  It is not good idea to add pointer into CALL_EXPR itself
     because we want to make possible having multiple cgraph nodes representing
     different clones of the same body before the body is actually cloned.  */
  for (e = node->callees; e; e= e->next_callee)
    {
      if (e->call_stmt == call_stmt)
	break;
      n++;
    }

  if (n > 100)
    {
      node->call_site_hash = htab_create_ggc (120, edge_hash, edge_eq, NULL);
      for (e2 = node->callees; e2; e2 = e2->next_callee)
	{
          void **slot;
          /* Skip fake edges.  */
          if (!e2->call_stmt)
	    continue;
	  slot = htab_find_slot_with_hash (node->call_site_hash,
					   e2->call_stmt,
					   htab_hash_pointer (e2->call_stmt),
					   INSERT);
	  gcc_assert (!*slot);
	  *slot = e2;
	}
    }

  return e;
}


/* Change field call_smt of edge E to NEW_STMT.  */

void
cgraph_set_call_stmt (struct cgraph_edge *e, gimple new_stmt)
{
  if (e->caller->call_site_hash)
    {
      htab_remove_elt_with_hash (e->caller->call_site_hash,
				 e->call_stmt,
				 htab_hash_pointer (e->call_stmt));
    }
  e->call_stmt = new_stmt;
  if (e->caller->call_site_hash)
    {
      void **slot;
      slot = htab_find_slot_with_hash (e->caller->call_site_hash,
				       e->call_stmt,
				       htab_hash_pointer
				       (e->call_stmt), INSERT);
      gcc_assert (!*slot);
      *slot = e;
    }
}

/* Create edge from CALLER to CALLEE in the cgraph.  */

struct cgraph_edge *
cgraph_create_edge (struct cgraph_node *caller, struct cgraph_node *callee,
		    gimple call_stmt, gcov_type count, int freq, int nest)
{
  struct cgraph_edge *edge;

#ifdef ENABLE_CHECKING
  /* This is rather pricely check possibly trigerring construction of call stmt
     hashtable.  */
  gcc_assert (!call_stmt /* a fake edge.  */
              || !cgraph_edge (caller, call_stmt));
#endif

  gcc_assert (!call_stmt || is_gimple_call (call_stmt));

  if (free_edges)
    {
      edge = free_edges;
      free_edges = NEXT_FREE_EDGE (edge);
    }
  else
    {
      edge = GGC_NEW (struct cgraph_edge);
      edge->uid = cgraph_edge_max_uid++;
    }

  if (!callee->analyzed)
    edge->inline_failed = N_("function body not available");
  else if (callee->local.redefined_extern_inline)
    edge->inline_failed = N_("redefined extern inline functions are not "
			     "considered for inlining");
  else if (callee->local.inlinable)
    edge->inline_failed = N_("function not considered for inlining");
  else
    edge->inline_failed = N_("function not inlinable");

  edge->aux = NULL;

  edge->caller = caller;
  edge->callee = callee;
  edge->call_stmt = call_stmt;
  edge->prev_caller = NULL;
  edge->next_caller = callee->callers;
  if (callee->callers)
    callee->callers->prev_caller = edge;
  edge->prev_callee = NULL;
  edge->next_callee = caller->callees;
  if (caller->callees)
    caller->callees->prev_callee = edge;
  caller->callees = edge;
  callee->callers = edge;
  edge->count = count;
  gcc_assert (count >= 0);
  edge->frequency = freq;
  gcc_assert (freq >= 0);
  gcc_assert (freq <= CGRAPH_FREQ_MAX);
  edge->loop_nest = nest;
  edge->indirect_call = 0;
  if (caller->call_site_hash)
    {
      void **slot;
      slot = htab_find_slot_with_hash (caller->call_site_hash,
				       edge->call_stmt,
				       htab_hash_pointer
					 (edge->call_stmt),
				       INSERT);
      gcc_assert (!*slot || !call_stmt);
      *slot = edge;
    }
  return edge;
}

/* Remove the edge E from the list of the callers of the callee.  */

static inline void
cgraph_edge_remove_callee (struct cgraph_edge *e)
{
  if (e->prev_caller)
    e->prev_caller->next_caller = e->next_caller;
  if (e->next_caller)
    e->next_caller->prev_caller = e->prev_caller;
  if (!e->prev_caller)
    e->callee->callers = e->next_caller;
}

/* Remove the edge E from the list of the callees of the caller.  */

static inline void
cgraph_edge_remove_caller (struct cgraph_edge *e)
{
  if (e->prev_callee)
    e->prev_callee->next_callee = e->next_callee;
  if (e->next_callee)
    e->next_callee->prev_callee = e->prev_callee;
  if (!e->prev_callee)
    e->caller->callees = e->next_callee;
  if (e->caller->call_site_hash && e->call_stmt)
    htab_remove_elt_with_hash (e->caller->call_site_hash,
			       e->call_stmt,
	  		       htab_hash_pointer (e->call_stmt));
}

/* Put the edge onto the free list.  */

static void
cgraph_free_edge (struct cgraph_edge *e)
{
  int uid = e->uid;

  /* Clear out the edge so we do not dangle pointers.  */
  memset (e, 0, sizeof (*e));
  e->uid = uid;
  NEXT_FREE_EDGE (e) = free_edges;
  free_edges = e;
}

/* Remove the edge E in the cgraph.  */

void
cgraph_remove_edge (struct cgraph_edge *e)
{
  /* Call all edge removal hooks.  */
  cgraph_call_edge_removal_hooks (e);

  /* Remove from callers list of the callee.  */
  cgraph_edge_remove_callee (e);

  /* Remove from callees list of the callers.  */
  cgraph_edge_remove_caller (e);

  /* Put the edge onto the free list.  */
  cgraph_free_edge (e);
}

/* Remove fake cgraph edges for indirect calls. NODE is the callee
   of the edges.  */

void
cgraph_remove_fake_indirect_call_in_edges (struct cgraph_node *node)
{
  struct cgraph_edge *f, *e;

  if (!L_IPO_COMP_MODE)
    return;

  for (e = node->callers; e; e = f)
    {
      f = e->next_caller;
      if (e->indirect_call && !e->call_stmt)
        cgraph_remove_edge (e);
    }
}


/* Redirect callee of E to N.  The function does not update underlying
   call expression.  */

void
cgraph_redirect_edge_callee (struct cgraph_edge *e, struct cgraph_node *n)
{
  /* Remove from callers list of the current callee.  */
  cgraph_edge_remove_callee (e);

  /* Insert to callers list of the new callee.  */
  e->prev_caller = NULL;
  if (n->callers)
    n->callers->prev_caller = e;
  e->next_caller = n->callers;
  n->callers = e;
  e->callee = n;
}


/* Update or remove the corresponding cgraph edge if a GIMPLE_CALL
   OLD_STMT changed into NEW_STMT.  */

void
cgraph_update_edges_for_call_stmt (gimple old_stmt, gimple new_stmt)
{
  tree new_call = (is_gimple_call (new_stmt)) ? gimple_call_fn (new_stmt) : 0;
  tree old_call = (is_gimple_call (old_stmt)) ? gimple_call_fn (old_stmt) : 0;
  struct cgraph_node *node = cgraph_node (cfun->decl);

  if (old_call != new_call)
    {
      struct cgraph_edge *e = cgraph_edge (node, old_stmt);
      struct cgraph_edge *ne = NULL;
      tree new_decl;

      if (e)
	{
	  gcov_type count = e->count;
	  int frequency = e->frequency;
	  int loop_nest = e->loop_nest;

	  cgraph_remove_edge (e);
	  if (new_call)
	    {
	      new_decl = gimple_call_fndecl (new_stmt);
	      if (new_decl)
		{
		  ne = cgraph_create_edge (node, cgraph_node (new_decl),
					   new_stmt, count, frequency,
					   loop_nest);
		  gcc_assert (ne->inline_failed);
		}
	    }
	}
    }
  else if (old_stmt != new_stmt)
    {
      struct cgraph_edge *e = cgraph_edge (node, old_stmt);

      if (e)
	cgraph_set_call_stmt (e, new_stmt);
    }
}


/* Remove all callees from the node.  */

void
cgraph_node_remove_callees (struct cgraph_node *node)
{
  struct cgraph_edge *e, *f;

  /* It is sufficient to remove the edges from the lists of callers of
     the callees.  The callee list of the node can be zapped with one
     assignment.  */
  for (e = node->callees; e; e = f)
    {
      f = e->next_callee;
      cgraph_call_edge_removal_hooks (e);
      cgraph_edge_remove_callee (e);
      cgraph_free_edge (e);
    }
  node->callees = NULL;
  if (node->call_site_hash)
    {
      htab_delete (node->call_site_hash);
      node->call_site_hash = NULL;
    }
}

/* Remove all callers from the node.  */

static void
cgraph_node_remove_callers (struct cgraph_node *node)
{
  struct cgraph_edge *e, *f;

  /* It is sufficient to remove the edges from the lists of callees of
     the callers.  The caller list of the node can be zapped with one
     assignment.  */
  for (e = node->callers; e; e = f)
    {
      f = e->next_caller;
      cgraph_call_edge_removal_hooks (e);
      cgraph_edge_remove_caller (e);
      cgraph_free_edge (e);
    }
  node->callers = NULL;
}

/* Release memory used to represent body of function NODE.  */

void
cgraph_release_function_body (struct cgraph_node *node)
{
  if (DECL_STRUCT_FUNCTION (node->decl))
    {
      tree old_decl = current_function_decl;
      push_cfun (DECL_STRUCT_FUNCTION (node->decl));
      if (cfun->gimple_df)
	{
	  current_function_decl = node->decl;
	  delete_tree_ssa ();
	  delete_tree_cfg_annotations ();
	  cfun->eh = NULL;
	  current_function_decl = old_decl;
	}
      if (cfun->cfg)
	{
	  gcc_assert (dom_computed[0] == DOM_NONE);
	  gcc_assert (dom_computed[1] == DOM_NONE);
	  clear_edges ();
	}
      if (cfun->value_histograms)
	free_histograms ();
      gcc_assert (!current_loops);
      pop_cfun();
      gimple_set_body (node->decl, NULL);
      VEC_free (ipa_opt_pass, heap,
      		DECL_STRUCT_FUNCTION (node->decl)->ipa_transforms_to_apply);
      /* Struct function hangs a lot of data that would leak if we didn't
         removed all pointers to it.   */
      ggc_free (DECL_STRUCT_FUNCTION (node->decl));
      DECL_STRUCT_FUNCTION (node->decl) = NULL;
    }
  DECL_SAVED_TREE (node->decl) = NULL;
  /* If the node is abstract and needed, then do not clear DECL_INITIAL
     of its associated function function declaration because it's
     needed to emit debug info later.  */
  if (!node->abstract_and_needed)
    DECL_INITIAL (node->decl) = error_mark_node;
}

/* Remove the node from cgraph.  */

void
cgraph_remove_node (struct cgraph_node *node)
{
  void **slot;
  bool kill_body = false;
  struct cgraph_node *n;
  int uid = node->uid;

  cgraph_call_node_removal_hooks (node);
  cgraph_node_remove_callers (node);
  cgraph_node_remove_callees (node);
  cgraph_remove_pid (node);

  /* Incremental inlining access removed nodes stored in the postorder list.
     */
  node->needed = node->reachable = false;
  for (n = node->nested; n; n = n->next_nested)
    n->origin = NULL;
  node->nested = NULL;
  if (node->origin)
    {
      struct cgraph_node **node2 = &node->origin->nested;

      while (*node2 != node)
	node2 = &(*node2)->next_nested;
      *node2 = node->next_nested;
    }
  if (node->previous)
    node->previous->next = node->next;
  else
    cgraph_nodes = node->next;
  if (node->next)
    node->next->previous = node->previous;
  node->next = NULL;
  node->previous = NULL;
  slot = htab_find_slot (cgraph_hash, node, NO_INSERT);
  if (*slot == node)
    {
      if (node->next_clone)
      {
	struct cgraph_node *new_node = node->next_clone;
	struct cgraph_node *n;

	/* Make the next clone be the master clone */
	for (n = new_node; n; n = n->next_clone)
	  n->master_clone = new_node;

	*slot = new_node;
	node->next_clone->prev_clone = NULL;
      }
      else
	{
	  htab_clear_slot (cgraph_hash, slot);
	  kill_body = true;
	}
    }
  else
    {
      node->prev_clone->next_clone = node->next_clone;
      if (node->next_clone)
	node->next_clone->prev_clone = node->prev_clone;
    }

  /* While all the clones are removed after being proceeded, the function
     itself is kept in the cgraph even after it is compiled.  Check whether
     we are done with this body and reclaim it proactively if this is the case.
     */
  if (!kill_body && *slot)
    {
      struct cgraph_node *n = (struct cgraph_node *) *slot;
      if (!n->next_clone && !n->global.inlined_to
	  && (cgraph_global_info_ready
	      && (TREE_ASM_WRITTEN (n->decl) || DECL_EXTERNAL (n->decl))))
	kill_body = true;
    }

  cgraph_remove_assembler_hash_node (node);

  if (kill_body)
    cgraph_release_function_body (node);

  cgraph_remove_link_node (node);

  node->decl = NULL;
  if (node->call_site_hash)
    {
      htab_delete (node->call_site_hash);
      node->call_site_hash = NULL;
    }
  cgraph_n_nodes--;

  /* Clear out the node to NULL all pointers and add the node to the free
     list.  */
  memset (node, 0, sizeof(*node));
  node->uid = uid;
  NEXT_FREE_NODE (node) = free_nodes;
  free_nodes = node;
}

/* Notify finalize_compilation_unit that given node is reachable.  */

void
cgraph_mark_reachable_node (struct cgraph_node *node)
{
  if (!node->reachable && node->local.finalized)
    {
      notice_global_symbol (node->decl);
      node->reachable = 1;
      gcc_assert (!cgraph_global_info_ready);

      node->next_needed = cgraph_nodes_queue;
      cgraph_nodes_queue = node;
    }
}

/* Likewise indicate that a node is needed, i.e. reachable via some
   external means.  */

void
cgraph_mark_needed_node (struct cgraph_node *node)
{
  node->needed = 1;
  cgraph_mark_reachable_node (node);
}

/* Indicate that the address of the function represented by the node
   has been taken.  */

void
cgraph_mark_address_taken (struct cgraph_node *node)
{
  node->address_taken = 1;
}

/* Return local info for the compiled function.  */

struct cgraph_local_info *
cgraph_local_info (tree decl)
{
  struct cgraph_node *node;

  gcc_assert (TREE_CODE (decl) == FUNCTION_DECL);
  node = cgraph_node (decl);
  return &node->local;
}

/* Return local info for the compiled function.  */

struct cgraph_global_info *
cgraph_global_info (tree decl)
{
  struct cgraph_node *node;

  gcc_assert (TREE_CODE (decl) == FUNCTION_DECL && cgraph_global_info_ready);
  node = cgraph_node (decl);
  return &node->global;
}

/* Return local info for the compiled function.  */

struct cgraph_rtl_info *
cgraph_rtl_info (tree decl)
{
  struct cgraph_node *node;

  gcc_assert (TREE_CODE (decl) == FUNCTION_DECL);
  node = cgraph_node (decl);
  if (decl != current_function_decl
      && !TREE_ASM_WRITTEN (node->decl))
    return NULL;
  return &node->rtl;
}

/* Return name of the node used in debug output.  */
const char *
cgraph_node_name (struct cgraph_node *node)
{
  return lang_hooks.decl_printable_name (node->decl, 2);
}

/* Names used to print out the availability enum.  */
const char * const cgraph_availability_names[] =
  {"unset", "not_available", "overwritable", "available", "local"};


/* Dump call graph node NODE to file F.  */

void
dump_cgraph_node (FILE *f, struct cgraph_node *node)
{
  struct cgraph_edge *edge;
  fprintf (f, "%s/%i(%i):", cgraph_node_name (node), node->uid, node->pid);
  if (node->global.inlined_to)
    fprintf (f, " (inline copy in %s/%i)",
	     cgraph_node_name (node->global.inlined_to),
	     node->global.inlined_to->uid);
  if (cgraph_function_flags_ready)
    fprintf (f, " availability:%s",
	     cgraph_availability_names [cgraph_function_body_availability (node)]);
  if (node->master_clone && node->master_clone->uid != node->uid)
    fprintf (f, "(%i)", node->master_clone->uid);
  if (node->count)
    fprintf (f, " executed "HOST_WIDEST_INT_PRINT_DEC"x",
	     (HOST_WIDEST_INT)node->count);
  if (node->max_bb_count)
    fprintf (f, " hottest bb executed "HOST_WIDEST_INT_PRINT_DEC"x",
	     (HOST_WIDEST_INT)node->max_bb_count);
  if (node->local.inline_summary.self_insns)
    fprintf (f, " %i insns", node->local.inline_summary.self_insns);
  if (node->local.inline_summary.self_hot_insns)
    fprintf (f, " %i hot insns", node->local.inline_summary.self_hot_insns);
  if (node->global.insns && node->global.insns
      != node->local.inline_summary.self_insns)
    fprintf (f, " (%i after inlining)", node->global.insns);
  if (node->local.inline_summary.estimated_self_stack_size)
    fprintf (f, " %i bytes stack usage", (int)node->local.inline_summary.estimated_self_stack_size);
  if (node->global.estimated_stack_size != node->local.inline_summary.estimated_self_stack_size)
    fprintf (f, " %i bytes after inlining", (int)node->global.estimated_stack_size);
  if (node->origin)
    fprintf (f, " nested in: %s", cgraph_node_name (node->origin));
  if (node->needed)
    fprintf (f, " needed");
  else if (node->reachable)
    fprintf (f, " reachable");
  if (gimple_has_body_p (node->decl))
    fprintf (f, " body");
  if (node->output)
    fprintf (f, " output");
  if (node->local.local)
    fprintf (f, " local");
  if (node->local.externally_visible)
    fprintf (f, " externally_visible");
  if (node->local.finalized)
    fprintf (f, " finalized");
  if (node->local.disregard_inline_limits)
    fprintf (f, " always_inline");
  else if (node->local.inlinable)
    fprintf (f, " inlinable");
  if (node->local.redefined_extern_inline)
    fprintf (f, " redefined_extern_inline");
  if (TREE_ASM_WRITTEN (node->decl))
    fprintf (f, " asm_written");

  fprintf (f, "\n  called by: ");
  for (edge = node->callers; edge; edge = edge->next_caller)
    {
      fprintf (f, "%s/%i ", cgraph_node_name (edge->caller),
	       edge->caller->uid);
      if (edge->count)
	fprintf (f, "("HOST_WIDEST_INT_PRINT_DEC"x) ",
		 (HOST_WIDEST_INT)edge->count);
      if (edge->frequency)
	fprintf (f, "(%.2f per call) ",
		 edge->frequency / (double)CGRAPH_FREQ_BASE);
      if (!edge->inline_failed)
	fprintf(f, "(inlined) ");
      if (edge->indirect_call)
	fprintf(f, "(indirect) ");
    }

  fprintf (f, "\n  calls: ");
  for (edge = node->callees; edge; edge = edge->next_callee)
    {
      fprintf (f, "%s/%i ", cgraph_node_name (edge->callee),
	       edge->callee->uid);
      if (!edge->inline_failed)
	fprintf(f, "(inlined) ");
      if (edge->indirect_call)
	fprintf(f, "(indirect) ");
      if (edge->count)
	fprintf (f, "("HOST_WIDEST_INT_PRINT_DEC"x) ",
		 (HOST_WIDEST_INT)edge->count);
      if (edge->frequency)
	fprintf (f, "(%.2f per call) ",
		 edge->frequency / (double)CGRAPH_FREQ_BASE);
      if (edge->loop_nest)
	fprintf (f, "(nested in %i loops) ", edge->loop_nest);
    }
  fprintf (f, "\n");
}


/* Dump call graph node NODE to stderr.  */

void
debug_cgraph_node (struct cgraph_node *node)
{
  dump_cgraph_node (stderr, node);
}


/* Dump the callgraph to file F.  */

void
dump_cgraph (FILE *f)
{
  struct cgraph_node *node;

  fprintf (f, "callgraph:\n\n");
  for (node = cgraph_nodes; node; node = node->next)
    dump_cgraph_node (f, node);
}


/* Dump the call graph to stderr.  */

void
debug_cgraph (void)
{
  dump_cgraph (stderr);
}


/* Set the DECL_ASSEMBLER_NAME and update cgraph hashtables.  */

void
change_decl_assembler_name (tree decl, tree name)
{
  gcc_assert (!assembler_name_hash);
  if (!DECL_ASSEMBLER_NAME_SET_P (decl))
    {
      SET_DECL_ASSEMBLER_NAME (decl, name);
      return;
    }
  if (name == DECL_ASSEMBLER_NAME (decl))
    return;

  if (TREE_SYMBOL_REFERENCED (DECL_ASSEMBLER_NAME (decl))
      && DECL_RTL_SET_P (decl))
    warning (0, "%D renamed after being referenced in assembly", decl);

  SET_DECL_ASSEMBLER_NAME (decl, name);
}

/* Add a top-level asm statement to the list.  */

struct cgraph_asm_node *
cgraph_add_asm_node (tree asm_str)
{
  struct cgraph_asm_node *node;

  node = GGC_CNEW (struct cgraph_asm_node);
  node->asm_str = asm_str;
  node->order = cgraph_order++;
  node->next = NULL;
  if (cgraph_asm_nodes == NULL)
    cgraph_asm_nodes = node;
  else
    cgraph_asm_last_node->next = node;
  cgraph_asm_last_node = node;
  return node;
}

/* Return true when the DECL can possibly be inlined.  */
bool
cgraph_function_possibly_inlined_p (tree decl)
{
  if (!cgraph_global_info_ready)
    return !DECL_UNINLINABLE (decl);
  return DECL_POSSIBLY_INLINED (decl);
}

/* Create clone of E in the node N represented by CALL_EXPR the callgraph.  */
struct cgraph_edge *
cgraph_clone_edge (struct cgraph_edge *e, struct cgraph_node *n,
		   gimple call_stmt, gcov_type count_scale, int freq_scale,
		   int loop_nest, bool update_original)
{
  struct cgraph_edge *new_edge;
  gcov_type count = e->count * count_scale / REG_BR_PROB_BASE;
  gcov_type freq = e->frequency * (gcov_type) freq_scale / CGRAPH_FREQ_BASE;

  if (freq > CGRAPH_FREQ_MAX)
    freq = CGRAPH_FREQ_MAX;
  new_edge = cgraph_create_edge (n, e->callee, call_stmt, count, freq,
                                 e->loop_nest + loop_nest);

  new_edge->inline_failed = e->inline_failed;
  new_edge->indirect_call = e->indirect_call;
  if (update_original)
    {
      e->count -= new_edge->count;
      if (e->count < 0)
	e->count = 0;
    }
  cgraph_call_edge_duplication_hooks (e, new_edge);
  return new_edge;
}

/* Create node representing clone of N executed COUNT times.  Decrease
   the execution counts from original node too.

   When UPDATE_ORIGINAL is true, the counts are subtracted from the original
   function's profile to reflect the fact that part of execution is handled
   by node.  */
struct cgraph_node *
cgraph_clone_node (struct cgraph_node *n, gcov_type count, int freq,
		   int loop_nest, bool update_original)
{
  struct cgraph_node *new_node = cgraph_create_node ();
  struct cgraph_edge *e;
  gcov_type count_scale;

  new_node->decl = n->decl;
  new_node->origin = n->origin;
  if (new_node->origin)
    {
      new_node->next_nested = new_node->origin->nested;
      new_node->origin->nested = new_node;
    }
  new_node->analyzed = n->analyzed;
  new_node->local = n->local;
  new_node->global = n->global;
  new_node->rtl = n->rtl;
  new_node->master_clone = n->master_clone;
  new_node->count = count;
  new_node->max_bb_count = count;
  if (n->count)
    new_node->max_bb_count = count * n->max_bb_count / n->count;
  new_node->is_versioned_clone = n->is_versioned_clone;
  if (n->count)
    {
      if (new_node->count > n->count)
        count_scale = REG_BR_PROB_BASE;
      else
        count_scale = new_node->count * REG_BR_PROB_BASE / n->count;
    }
  else
    count_scale = 0;
  if (update_original)
    {
      n->count -= count;
      if (n->count < 0)
	n->count = 0;
      n->max_bb_count -= new_node->max_bb_count;
      if (n->max_bb_count < 0)
	n->max_bb_count = 0;
    }

  for (e = n->callees;e; e=e->next_callee)
    cgraph_clone_edge (e, new_node, e->call_stmt, count_scale, freq, loop_nest,
		       update_original);

  new_node->next_clone = n->next_clone;
  new_node->prev_clone = n;
  n->next_clone = new_node;
  if (new_node->next_clone)
    new_node->next_clone->prev_clone = new_node;

  cgraph_call_node_duplication_hooks (n, new_node);
  return new_node;
}

/* Return true if N is an master_clone, (see cgraph_master_clone).  */

bool
cgraph_is_master_clone (struct cgraph_node *n)
{
  return (n == cgraph_master_clone (n));
}

struct cgraph_node *
cgraph_master_clone (struct cgraph_node *n)
{
  enum availability avail = cgraph_function_body_availability (n);

  if (avail == AVAIL_NOT_AVAILABLE || avail == AVAIL_OVERWRITABLE)
    return NULL;

  if (!n->master_clone)
    n->master_clone = cgraph_node (n->decl);

  return n->master_clone;
}

/* NODE is no longer nested function; update cgraph accordingly.  */
void
cgraph_unnest_node (struct cgraph_node *node)
{
  struct cgraph_node **node2 = &node->origin->nested;
  gcc_assert (node->origin);

  while (*node2 != node)
    node2 = &(*node2)->next_nested;
  *node2 = node->next_nested;
  node->origin = NULL;
}

/* Return function availability.  See cgraph.h for description of individual
   return values.  */
enum availability
cgraph_function_body_availability (struct cgraph_node *node)
{
  enum availability avail;
  gcc_assert (cgraph_function_flags_ready);
  if (!node->analyzed)
    avail = AVAIL_NOT_AVAILABLE;
  else if (node->local.local)
    avail = AVAIL_LOCAL;
  else if (!node->local.externally_visible)
    avail = AVAIL_AVAILABLE;

  /* If the function can be overwritten, return OVERWRITABLE.  Take
     care at least of two notable extensions - the COMDAT functions
     used to share template instantiations in C++ (this is symmetric
     to code cp_cannot_inline_tree_fn and probably shall be shared and
     the inlinability hooks completely eliminated).

     ??? Does the C++ one definition rule allow us to always return
     AVAIL_AVAILABLE here?  That would be good reason to preserve this
     hook Similarly deal with extern inline functions - this is again
     necessary to get C++ shared functions having keyed templates
     right and in the C extension documentation we probably should
     document the requirement of both versions of function (extern
     inline and offline) having same side effect characteristics as
     good optimization is what this optimization is about.  */

  else if (!(*targetm.binds_local_p) (node->decl)
	   && !DECL_COMDAT (node->decl) && !DECL_EXTERNAL (node->decl))
    avail = AVAIL_OVERWRITABLE;
  else avail = AVAIL_AVAILABLE;

  return avail;
}

/* Add the function FNDECL to the call graph.
   Unlike cgraph_finalize_function, this function is intended to be used
   by middle end and allows insertion of new function at arbitrary point
   of compilation.  The function can be either in high, low or SSA form
   GIMPLE.

   The function is assumed to be reachable and have address taken (so no
   API breaking optimizations are performed on it).  

   Main work done by this function is to enqueue the function for later
   processing to avoid need the passes to be re-entrant.  */

void
cgraph_add_new_function (tree fndecl, bool lowered)
{
  struct cgraph_node *node;
  switch (cgraph_state)
    {
      case CGRAPH_STATE_CONSTRUCTION:
	/* Just enqueue function to be processed at nearest occurrence.  */
	node = cgraph_node (fndecl);
	node->next_needed = cgraph_new_nodes;
	if (lowered)
	  node->lowered = true;
	cgraph_new_nodes = node;
        break;

      case CGRAPH_STATE_IPA:
      case CGRAPH_STATE_IPA_SSA:
      case CGRAPH_STATE_EXPANSION:
	/* Bring the function into finalized state and enqueue for later
	   analyzing and compilation.  */
	node = cgraph_node (fndecl);
	node->local.local = false;
	node->local.finalized = true;
	node->reachable = node->needed = true;
	if (!lowered && cgraph_state == CGRAPH_STATE_EXPANSION)
	  {
	    push_cfun (DECL_STRUCT_FUNCTION (fndecl));
	    current_function_decl = fndecl;
	    gimple_register_cfg_hooks ();
	    tree_lowering_passes (fndecl);
	    bitmap_obstack_initialize (NULL);
	    if (!gimple_in_ssa_p (DECL_STRUCT_FUNCTION (fndecl)))
	      execute_pass_list (pass_early_local_passes.pass.sub);
	    bitmap_obstack_release (NULL);
	    pop_cfun ();
	    current_function_decl = NULL;

	    lowered = true;
	  }
	if (lowered)
	  node->lowered = true;
	node->next_needed = cgraph_new_nodes;
	cgraph_new_nodes = node;
        break;

      case CGRAPH_STATE_FINISHED:
	/* At the very end of compilation we have to do all the work up
	   to expansion.  */
	push_cfun (DECL_STRUCT_FUNCTION (fndecl));
	current_function_decl = fndecl;
	gimple_register_cfg_hooks ();
	if (!lowered)
          tree_lowering_passes (fndecl);
	bitmap_obstack_initialize (NULL);
	if (!gimple_in_ssa_p (DECL_STRUCT_FUNCTION (fndecl)))
	  execute_pass_list (pass_early_local_passes.pass.sub);
	bitmap_obstack_release (NULL);
	tree_rest_of_compilation (fndecl);
	pop_cfun ();
	current_function_decl = NULL;
	break;
    }
}


/* Return a integer between 1 and RANGE based on the magnitude of VALUE
   relative to MAX_VALUE on a log scale.  More precisely, returns:
     log2(VALUE) - log2(MAX_VALUE) + RANGE
   For example, if VALUE ~= MAX_VALUE, return RANGE; if VALUE ~= MAX_VALUE/2,
   return RANGE - 1; if VALUE ~= MAX_VALUE/4, return RANGE - 2;   etc.
   Used in DUMP_VCG_CGRAPH to generate line widths of graph elements.  */

static int
relative_log_magnitude (int value, int max_value, int range)
{
  int width;
  if (value <= 0 || max_value <= 0)
    return 1;
  width = floor_log2 (value) - floor_log2 (max_value) + range;
  if (width < 1)
    width = 1;
  return width;
}


/* Dump a graphical representation of the call graph to FP in VCG
   format.  MIN_COUNT is minimum execution count of nodes for inclusion
   in the dumped graph.  If WEIGHTED is true, then scale the line
   width of nodes and edges based on count if counts are available or
   frequency otherwise.  */

void
dump_vcg_cgraph (FILE *fp, int min_count, bool weighted)
{
  struct cgraph_node *node;
  struct cgraph_edge *edge;
  gcov_type max_count = 0;
  bool *include_node;

  for (node = cgraph_nodes; node; node = node->next)
    if (max_count < node->count)
      max_count = node->count;

  /* Find nodes to include in call graph based on MIN_COUNT
     threshold.  */
  include_node = XCNEWVEC (bool, cgraph_max_uid);
  for (node = cgraph_nodes; node; node = node->next)
    {
      /* Include NODE in graph if any of the following conditions is
	 met:
	   1) Count of NODE is at least MIN_COUNT.
           2) NODE has an inlined callsite (edge) with a count of at least
	      MIN_COUNT.  This includes callsites inlined transitively beneath
	      NODE.
	   3) Count of an edge extending from NODE is at least MIN_COUNT.  */
      if (node->count >= min_count)
	{
	  include_node[node->uid] = true;
	  if (node->global.inlined_to)
	    {
	      /* Include nodes that NODE is inlined into.  */
	      for (edge = node->callers;
		   edge && !edge->inline_failed;
		   edge = edge->caller->callers)
		include_node[edge->caller->uid] = true;
	    }
	}
      else
	{
	  for (edge = node->callees; edge; edge = edge->next_callee)
	    if (edge->count >= min_count)
	      {
		include_node[node->uid] = true;
		break;
	      }
	}
    }

  fprintf (fp, "graph: {\n");
  fprintf (fp, "  title: \"%s\"\n", main_input_filename);
  for (node = cgraph_nodes; node; node = node->next)
    {
      unsigned int i, pos;
      const char *node_name = cgraph_node_name(node);
      if (!include_node[node->uid])
	continue;
      /* Use UID as a title because uniqueness is required, but use
	 function name as the label.  */
      fprintf (fp, "  node: { title:\"%d\" label:\"", node->uid);
      /* Word wrap label if node name exceeds 40 characters because
	 templated functions can have ridiculously long names which
	 skews the graph.  */
      pos = 0;
      for (i = 0; i < strlen(node_name); i++)
	{
	  if (pos > 40 && node_name[i] == ' ')
	    {
	      fprintf (fp, "\\n  ");
	      pos = 2;
	    }
	  else
	    {
	      fprintf (fp, "%c", node_name[i]);
	      pos++;
	    }
	}
      fprintf (fp, "\" info1:\"count=" HOST_WIDEST_INT_PRINT_DEC "\"",
	       node->count);
      /* info2 field holds the type of node, either inlined, external
        (outside this compilation unit), or "normal".  */
      if (node->global.inlined_to)
	{
	  fprintf (fp, " info2:\"inlined\"");
	  /* Make inlined nodes gray.  */
	  fprintf (fp, " textcolor:lightgrey bordercolor:lightgrey");
	}
      else if (!node->analyzed)
	{
	  fprintf (fp, " info2:\"external\"");
	  /* Give nodes outside this compilation unit a gray background.  */
	  fprintf (fp, " color:lightgrey");
	}
      else
	fprintf (fp, " info2:\"normal\"");

      if (weighted && max_count)
	fprintf (fp, " borderwidth:%d",
		 relative_log_magnitude (node->count, max_count, 10));
      fprintf (fp, " }\n");
    }

  for (node = cgraph_nodes; node; node = node->next)
    for (edge = node->callees; edge; edge = edge->next_callee)
      /* Include edge in graph only if source and destination are in
	 the graph, and also the edge must be of minimum count or be a
	 inlined edge (in which case, the edge is necessarily on a
	 path connecting a node of minimum count).  */
      if (include_node[edge->caller->uid] && include_node[edge->callee->uid]
	  && (!edge->inline_failed || edge->count >= min_count))
	{
	  fprintf (fp, "  edge: { sourcename:\"%d\" targetname:\"%d\"",
		   edge->caller->uid, edge->callee->uid);
	  /* Label edge with count and frequency.  By default this
	     label is not shown, so such a long string generally
	     doesn't muck up the graph.  */
	  fprintf (fp, " label:\"count=" HOST_WIDEST_INT_PRINT_DEC
		   ",freq=%0.4f\"",
		   edge->count, (float)(edge->frequency)/CGRAPH_FREQ_BASE);
	  /* Make inlined edges gray and class 2.  Xvcg can toggle
	     visibility of edges by class, so deselecting class 2
	     edges collapses all inlined nodes into the top level
	     caller into which the nodes are inlined.  */
	  if (!edge->inline_failed)
	    fprintf (fp, " color:lightgrey class:2");

	  if (weighted)
	    {
	      /* Weight by count if profile counts are available
		 otherwise use frequency.  */
	      int width;
	      if (max_count)
		width = relative_log_magnitude (edge->count, max_count, 10);
	      else
		width = relative_log_magnitude (edge->frequency,
						CGRAPH_FREQ_MAX, 10);
	      fprintf (fp, " thickness:%d arrowsize:%d", width, width + 8);
	    }

	  fprintf (fp, " }\n");
	}

  fprintf (fp, "}\n");
  free (include_node);
}

/* Return true if NODE is a hot function.  */

bool
hot_function_p (struct cgraph_node *node)
{
  struct cgraph_edge *edge;

  if (node->local.inline_summary.self_hot_insns > 0)
    return true;

  for (edge = node->callees; edge; edge = edge->next_callee)
    if (cgraph_maybe_hot_edge_p (edge))
      return true;

  for (edge = node->callers; edge; edge = edge->next_caller)
    if (cgraph_maybe_hot_edge_p (edge))
      return true;

  return false;
}

#include "gt-cgraph.h"
