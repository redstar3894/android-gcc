/* Redundant Zero-extension elimination for targets that implicitly
   zero-extend writes to the lower 32-bit portion of 64-bit registers.
   Copyright (C) 2009 Free Software Foundation, Inc.
   Contributed by Sriraman Tallam (tmsriram@google.com) and
                  Silvius Rus     (rus@google.com)

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
<http://www.gnu.org/licenses/>. */


/* Problem Description :
  ---------------------

This pass is intended to be applicable only to targets that implicitly
zero-extend 64-bit registers after writing to their lower 32-bit half.
For instance, x86_64 zero-extends the upper bits of a register
implicitly whenever an instruction writes to its lower 32-bit half.
For example, the instruction *add edi,eax* also zero-extends the upper
32-bits of rax after doing the addition.  These zero extensions come
for free and GCC does not always exploit this well.  That is, it has
been observed that there are plenty of cases where GCC explicitly
zero-extends registers for x86_64 that are actually useless because
these registers were already implicitly zero-extended in a prior
instruction.  This pass tries to eliminate such useless zero extension
instructions.

How does this pass work  ?
--------------------------

This pass is run after register allocation.  Hence, all registers that
this pass deals with are hard registers.  This pass first looks for a
zero-extension instruction that could possibly be redundant. Such zero
extension instructions show up in RTL with the pattern :
(set (reg:DI x) (zero_extend:DI (reg:SI x))).
where x can be any one of the 64-bit hard registers.
Now, this pass tries to eliminate this instruction by merging the
zero-extension with the definitions of register x. For instance, if
one of the definitions of register x was  :
(set (reg:SI x) (plus:SI (reg:SI z1) (reg:SI z2))),
then the combination converts this into :
(set (reg:DI x) (zero_extend:DI (plus:SI (reg:SI z1) (reg:SI z2)))).
If all the merged definitions are recognizable assembly instructions,
the zero-extension is effectively eliminated.  For example, in x86_64,
implicit zero-extensions are captured with appropriate patterns in the
i386.md file.  Hence, these merged definition can be matched to a single
assembly instruction.  The original zero-extension instruction is then
deleted if all the definitions can be merged.

However, there are cases where the definition instruction cannot be
merged with a zero-extend.  Examples are CALL instructions.  In such
cases, the original zero extension is not redundant and this pass does
not delete it.

Handling conditional moves :
----------------------------

Architectures like x86_64 support conditional moves whose semantics for
zero-extension differ from the other instructions.  For instance, the
instruction *cmov ebx, eax*
zero-extends eax onto rax only when the move from ebx to eax happens.
Otherwise, eax may not be zero-extended.  Conditional moves appear as
RTL instructions of the form
(set (reg:SI x) (if_then_else (cond) (reg:SI y) (reg:SI z))).
This pass tries to merge a zero-extension with a conditional move by
actually merging the defintions of y and z with a zero-extend and then
converting the conditional move into :
(set (reg:DI x) (if_then_else (cond) (reg:DI y) (reg:DI z))).
Since registers y and z are zero-extended, register x will also be
zero-extended after the conditional move.  Note that this step has to
be done transitively since the definition of a conditional copy can be
another conditional copy.

Motivating Example I :
---------------------
For this program :
**********************************************
bad_code.c

int mask[1000];

int foo(unsigned x)
{
  if (x < 10)
    x = x * 45;
  else
    x = x * 78;
  return mask[x];
}
**********************************************

$ gcc -O2 -fsee bad_code.c (Turned on existing sign-extension elimination.)
  ........
  400315:       b8 4e 00 00 00          mov    $0x4e,%eax
  40031a:       0f af f8                imul   %eax,%edi
  40031d:       89 ff                   mov    %edi,%edi  ---> Useless extend.
  40031f:       8b 04 bd 60 19 40 00    mov    0x401960(,%rdi,4),%eax
  400326:       c3                      retq
  ......
  400330:       ba 2d 00 00 00          mov    $0x2d,%edx
  400335:       0f af fa                imul   %edx,%edi
  400338:       89 ff                   mov    %edi,%edi  ---> Useless extend.
  40033a:       8b 04 bd 60 19 40 00    mov    0x401960(,%rdi,4),%eax
  400341:       c3                      retq

$ gcc -O2 -fzee bad_code.c
  ......
  400315:       6b ff 4e                imul   $0x4e,%edi,%edi
  400318:       8b 04 bd 40 19 40 00    mov    0x401940(,%rdi,4),%eax
  40031f:       c3                      retq
  400320:       6b ff 2d                imul   $0x2d,%edi,%edi
  400323:       8b 04 bd 40 19 40 00    mov    0x401940(,%rdi,4),%eax
  40032a:       c3                      retq

Motivating Example II :
---------------------

Here is an example with a conditional move.

For this program :
**********************************************

unsigned long long foo(unsigned x , unsigned y)
{
  unsigned z;
  if (x > 100)
    z = x + y;
  else
    z = x - y;
  return (unsigned long long)(z);
}

$ gcc -O2 -fsee bad_code.c (Turned on existing sign-extension elimination.)
  ............
  400360:       8d 14 3e                lea    (%rsi,%rdi,1),%edx
  400363:       89 f8                   mov    %edi,%eax
  400365:       29 f0                   sub    %esi,%eax
  400367:       83 ff 65                cmp    $0x65,%edi
  40036a:       0f 43 c2                cmovae %edx,%eax
  40036d:       89 c0                   mov    %eax,%eax ---> Useless extend.
  40036f:       c3                      retq

$ gcc -O2 -fzee bad_code.c
  .............
  400360:       89 fa                   mov    %edi,%edx
  400362:       8d 04 3e                lea    (%rsi,%rdi,1),%eax
  400365:       29 f2                   sub    %esi,%edx
  400367:       83 ff 65                cmp    $0x65,%edi
  40036a:       89 d6                   mov    %edx,%esi
  40036c:       48 0f 42 c6             cmovb  %rsi,%rax
  400370:       c3                      retq


Usefulness :
----------

This pass reduces the dynamic instruction count of a compression benchmark by
2.8% and improves it run-time by about 1%.  The compression benchmark had the
following code sequence in a very hot region of code before ZEE optimized it :

shr $0x5, %edx
mov %edx, %edx --> Useless zero-extend.

How to turn on ?
----------------
-fzee -O2

*/

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "rtl.h"
#include "tree.h"
#include "tm_p.h"
#include "flags.h"
#include "regs.h"
#include "hard-reg-set.h"
#include "basic-block.h"
#include "insn-config.h"
#include "function.h"
#include "expr.h"
#include "insn-attr.h"
#include "recog.h"
#include "real.h"
#include "toplev.h"
#include "target.h"
#include "timevar.h"
#include "optabs.h"
#include "insn-codes.h"
#include "rtlhooks-def.h"
/* Include output.h for dump_file.  */
#include "output.h"
#include "params.h"
#include "timevar.h"
#include "tree-pass.h"
#include "df.h"
#include "cgraph.h"

/* This says if a register is newly created for the purpose of
   zero-extension. */

enum insn_merge_code
{
  MERGE_NOT_ATTEMPTED = 0,
  MERGE_SUCCESS
};

/* This says if a INSN UID or its definition has already been merged
   with a zero-extend or not. */

static enum insn_merge_code *is_insn_merge_attempted;
static int max_insn_uid;

/* Get and Set methods for is_insn_merge_attempted */

static enum insn_merge_code
get_insn_status (rtx insn)
{
  gcc_assert (INSN_UID (insn) < max_insn_uid);
  return is_insn_merge_attempted[INSN_UID (insn)];
}

static void
set_insn_status (rtx insn, enum insn_merge_code code)
{
  gcc_assert (INSN_UID (insn) < max_insn_uid);
  is_insn_merge_attempted[INSN_UID (insn)] = code;
}

/* Check to see if this zero-extend matches a pattern
   that could be eliminated.  This is called via
   for_each_rtx in function find_and_remove_ze. */

static int
is_set_with_extension_DI (rtx *expr, void *data)
{
  /* Looking only for patterns of the type :
     SET (REG:DI X) (ZERO_EXTEND (REG:SI x))
   */

  if (GET_CODE (*expr) == SET
      && GET_MODE (SET_DEST (*expr)) == DImode
      && GET_CODE (SET_DEST (*expr)) == REG)
    {
      if (GET_CODE (SET_SRC (*expr)) == ZERO_EXTEND
          && GET_CODE (XEXP (SET_SRC (*expr),0)) == REG
          && GET_MODE (XEXP (SET_SRC (*expr),0)) == SImode
          && REGNO (SET_DEST (*expr)) == REGNO (XEXP (SET_SRC (*expr),0)))
            {
              *(rtx **)(data) = expr;
              return 1;
            }
    }
  return 0;
}

/* Given a insn and a pointer to the SET rtx that needs to be
   modified, this code modifies the SET rtx to a new SET rtx
   that zero_extends the right hand expression into a DImode
   register on the left hand side.  Note that multiple
   assumptions are made about the nature of the set that needs
   to be true for this to work and is called from merge_def_and_ze.

   Original :
   (set (reg:SI a) (expression))

   Transform :
   (set (reg:DI a) (zero_extend (expression)))

   Special Cases :
   If the expression is a constant or another zero_extend directly
   assign it to the 64-bit register.
*/

static bool
combine_set_zero_extend (rtx curr_insn, rtx *orig_set, rtx newreg)
{
  rtx temp_extension, simplified_temp_extension, new_set, new_const_int;
  rtx orig_src,orig_dest;
  HOST_WIDE_INT val;

  /* Change the SET rtx and validate it. */
  orig_src = SET_SRC (*orig_set);
  orig_dest = SET_DEST (*orig_set);
  new_set = NULL_RTX;

  /* The right hand side can also be VOIDmode.  These cases have to be
     handled differently. */

  if (GET_MODE (orig_src) != SImode)
    {
      /* Merge constants by directly moving the constant into the
         64-bit register under some conditions. */

      if (GET_CODE (orig_src) == CONST_INT)
        {
          if (INTVAL (orig_src) >= 0 && INTVAL (orig_src) <= 0x7fffffff)
            {
              new_set = gen_rtx_SET (VOIDmode, newreg, orig_src);
            }
          else if (INTVAL (orig_src) < 0)
            {
              val = INTVAL (orig_src);

              /* Zero-extending a negative 32-bit integer into 64-bits makes
                 it a positive integer.  Convert the given negative integer
                 into the appropriate postive integer when zero-extended. */

              val = 0xffffffff + val + 1;
              gcc_assert (val > 0);
              new_const_int = gen_rtx_CONST_INT (VOIDmode, val);
              new_set = gen_rtx_SET (VOIDmode, newreg, new_const_int);
            }
          else
            {
              return false;
            }
        }
      else
        {
          /* This is mostly due to a call insn that should not be
             optimized. */

          return false;
        }
    }
  else if (GET_CODE (orig_src) == ZERO_EXTEND)
    {
      /* Here a zero-extend is used to get to SI. Why not make it
         all the  way till DI. */

      temp_extension = gen_rtx_ZERO_EXTEND (DImode, XEXP (orig_src, 0));
      simplified_temp_extension = simplify_rtx (temp_extension);
      if (simplified_temp_extension)
        temp_extension = simplified_temp_extension;
      new_set = gen_rtx_SET (VOIDmode, newreg, temp_extension);
    }
  else if (GET_CODE (orig_src) == IF_THEN_ELSE)
    {
      /* Only IF_THEN_ELSE of phi-type copies are combined. Otherwise,
         in general, IF_THEN_ELSE should not be combined. */

      return false;
    }
  else
    {
      /* This is the normal case we expect. */

      temp_extension = gen_rtx_ZERO_EXTEND (DImode, orig_src);
      simplified_temp_extension = simplify_rtx (temp_extension);
      if (simplified_temp_extension)
        temp_extension = simplified_temp_extension;
      new_set = gen_rtx_SET (VOIDmode, newreg, temp_extension);
    }

  gcc_assert (new_set != NULL_RTX);

  /* This change is a part of a group of changes. Hence,
     validate_change will not try to commit the change. */

  if (validate_change (curr_insn, orig_set, new_set, true))
    {
      if (dump_file)
        {
          fprintf (dump_file, "Merged Instruction with ZERO_EXTEND:\n");
          print_rtl_single (dump_file, curr_insn);
        }
      return true;
    }
  return false;
}

/* This returns the DI mode for the SI register. */

static rtx
get_reg_di (rtx reg_si)
{
  rtx newreg;

  newreg = gen_rtx_REG (DImode, REGNO (reg_si));
  gcc_assert (newreg);
  return newreg;
}

/* Treat if_then_else insns, where the operands of both branches
   are registers, as copies. For instance,
   Original :
   (set (reg:SI a) (if_then_else (cond) (reg:SI b) (reg:SI c)))
   Transformed :
   (set (reg:DI a) (if_then_else (cond) (reg:DI b) (reg:DI c))) */

static bool
transform_ifelse (rtx def_insn)
{
  rtx set_insn = PATTERN (def_insn);
  rtx srcreg, dstreg, srcreg2;
  rtx map_srcreg, map_dstreg, map_srcreg2;
  rtx ifexpr;
  rtx cond;
  rtx new_set;

  gcc_assert (GET_CODE (set_insn) == SET);
  cond = XEXP (SET_SRC (set_insn), 0);
  dstreg = SET_DEST (set_insn);
  srcreg = XEXP (SET_SRC (set_insn), 1);
  srcreg2 = XEXP (SET_SRC (set_insn), 2);
  map_srcreg = get_reg_di (srcreg);
  map_srcreg2 = get_reg_di (srcreg2);
  map_dstreg = get_reg_di (dstreg);
  ifexpr = gen_rtx_IF_THEN_ELSE (DImode, cond, map_srcreg, map_srcreg2);
  new_set = gen_rtx_SET (VOIDmode, map_dstreg, ifexpr);

  if (validate_change (def_insn, &PATTERN (def_insn), new_set, true))
    {
      if (dump_file)
        {
          fprintf (dump_file, "Cond_Move Instruction's mode extended :\n");
          print_rtl_single (dump_file, def_insn);
        }
      return true;
    }
  else
    return false;
}

/* Function to get all the immediate definitions of an instruction.
   The reaching definitions are desired for which_reg used in
   curr_insn.  This function returns 0 if there was an error getting
   a definition.  Upon success, this function returns the number of
   definitions. */

static int
get_defs (rtx curr_insn, rtx which_reg, VEC (rtx,heap) **dest)
{
  df_ref reg_info, *defs;
  struct df_link *def_chain;
  int n_refs = 0;

  defs = DF_INSN_USES (curr_insn);
  reg_info = NULL;

  while (*defs)
    {
      reg_info = *defs;
      if (GET_CODE (DF_REF_REG (reg_info)) == SUBREG)
        {
          return 0;
        }
      if (REGNO (DF_REF_REG (reg_info)) == REGNO (which_reg))
        {
          break;
        }
      defs++;
    }

  gcc_assert (reg_info != NULL && defs != NULL);
  def_chain = DF_REF_CHAIN (reg_info);

  while (def_chain)
    {
      /* Problem getting some definition for this instruction */

      if (def_chain->ref == NULL)
        {
          return 0;
        }
      if (DF_REF_INSN_INFO (def_chain->ref) == NULL)
        {
          return 0;
        }
      def_chain = def_chain->next;
    }

  def_chain = DF_REF_CHAIN (reg_info);

  if (dest == NULL)
    return 1;

  while (def_chain)
    {
      VEC_safe_push (rtx, heap, *dest, DF_REF_INSN (def_chain->ref));
      def_chain = def_chain->next;
      n_refs++;
    }
  return n_refs;
}

/* rtx function to check if this SET insn is a conditional copy insn :
   (set (reg:SI a ) (IF_THEN_ELSE (cond) (reg:SI b) (reg:SI c)))
   Called from is_insn_cond_copy */

static int
is_this_a_cmove (rtx expr, void *data)
{
  /* Check for conditional (if-then-else) copy. */

  if (GET_CODE (expr) == SET
      && GET_CODE (SET_DEST (expr)) == REG
      && GET_MODE (SET_DEST (expr)) == SImode
      && GET_CODE (SET_SRC (expr))  == IF_THEN_ELSE
      && GET_CODE (XEXP (SET_SRC (expr), 1)) == REG
      && GET_MODE (XEXP (SET_SRC (expr), 1)) == SImode
      && GET_CODE (XEXP (SET_SRC (expr), 2)) == REG
      && GET_MODE (XEXP (SET_SRC (expr), 2)) == SImode)
    {
      ((rtx *)data)[0] = XEXP (SET_SRC (expr), 1);
      ((rtx *)data)[1] = XEXP (SET_SRC (expr), 2);
      return 1;
    }
  return 0;
}

/* This returns 1 if it found
   (SET (reg:SI REGNO (def_reg)) (if_then_else (cond) (REG:SI x1) (REG:SI x2)))
   in its pattern.  It stores the x1 and x2 in copy_reg_1 and copy_reg_2. */

static int
is_insn_cond_copy (rtx def_insn, rtx *copy_reg_1, rtx *copy_reg_2)
{
  int type;
  rtx set_expr;
  rtx srcreg[2];

  srcreg[0] = NULL_RTX;
  srcreg[1] = NULL_RTX;

  set_expr = single_set (def_insn);

  if (set_expr == NULL_RTX)
    return 0;

  type = is_this_a_cmove (set_expr, (void *) srcreg);

  if (type)
    {
      *copy_reg_1 = srcreg[0];
      *copy_reg_2 = srcreg[1];
      return type;
    }

  return 0;
}

/* Reaching Definitions of the zero-extended register could be conditional
   copies or regular definitions.  This function separates the two types into
   two lists.  This is necessary because, if a reaching definition is a
   conditional copy, combining the zero_extend with this definition is wrong.
   Conditional copies are merged by transitively merging its definitions.
   The defs_list is populated with all the reaching definitions of the
   zero-extension instruction (zero_extend_insn) which must be merged with
   a zero_extend.  The copies_list contains all the conditional moves that
   will later be extended into a DI mode conditonal move if all the merges
   are successful.  The function returns false when there is a failure in
   getting some definitions, like that of parameters.  It returns 1 upon
   success, 0 upon failure and 2 when all definitions of the zero_extend_insn
   were merged previously. */

static int
make_defs_and_copies_lists (rtx zero_extend_insn, rtx set_pat,
                            VEC (rtx,heap) **defs_list,
                            VEC (rtx,heap) **copies_list)
{
  bool *is_insn_visited;
  VEC (rtx,heap) *work_list;
  rtx srcreg, copy_reg_1, copy_reg_2;
  rtx def_insn;
  int n_defs = 0;
  int vec_index = 0;
  int n_worklist = 0;
  int i, is_copy;

  srcreg = XEXP (SET_SRC (set_pat), 0);
  work_list = VEC_alloc (rtx, heap, 8);

  is_insn_visited = XNEWVEC (bool, max_insn_uid);

  for (i = 0; i < max_insn_uid; i++)
    is_insn_visited[i] = false;

  /* Initialize the Work List */
  n_worklist = get_defs (zero_extend_insn, srcreg, &work_list);

  if (n_worklist == 0)
    {
      VEC_free (rtx, heap, work_list);
      XDELETEVEC (is_insn_visited);
      /* The number of defs being equal to zero can only imply that all of its
         definitions have been previously merged. */
      return 2;
    }

  /* Perform transitive closure for conditional copies. */
  while (n_worklist > vec_index)
    {
      def_insn = VEC_index (rtx, work_list, vec_index);
      gcc_assert (INSN_UID (def_insn) < max_insn_uid);

      if (is_insn_visited[INSN_UID (def_insn)])
        {
          vec_index++;
          continue;
        }

      is_insn_visited[INSN_UID (def_insn)] = true;
      copy_reg_1 = copy_reg_2 = NULL_RTX;
      is_copy = is_insn_cond_copy (def_insn, &copy_reg_1, &copy_reg_2);
      if (is_copy)
        {
          gcc_assert (copy_reg_1 && copy_reg_2);

          /* Push it into the copy list first. */

          VEC_safe_push (rtx, heap, *copies_list, def_insn);

          /* Perform transitive closure here */

          n_defs = 0;
          n_defs = get_defs (def_insn, copy_reg_1, &work_list);

          if (n_defs == 0)
            {
              VEC_free (rtx, heap, work_list);
              XDELETEVEC (is_insn_visited);
              return 0;
            }
          n_worklist += n_defs;

          n_defs = 0;
          n_defs = get_defs (def_insn, copy_reg_2, &work_list);
          if (n_defs == 0)
            {
              VEC_free (rtx, heap, work_list);
              XDELETEVEC (is_insn_visited);
              return 0;
            }
          n_worklist += n_defs;
        }
      else
        {
          VEC_safe_push (rtx, heap, *defs_list, def_insn);
        }
      vec_index++;
    }

  VEC_free (rtx, heap, work_list);
  XDELETEVEC (is_insn_visited);
  return 1;
}

/* Merge the definition with a zero-extend.  Calls combine_set_zero_extend
   on the SET pattern. */

static bool
merge_def_and_ze (rtx def_insn)
{
  enum rtx_code code;
  rtx setreg;
  rtx *sub_rtx;
  rtx s_expr;
  int i;

  code = GET_CODE (PATTERN (def_insn));
  sub_rtx = NULL;

  if (code == PARALLEL)
    {
      for (i = 0; i < XVECLEN (PATTERN (def_insn), 0); i++)
        {
          s_expr = XVECEXP (PATTERN (def_insn), 0, i);
          if (GET_CODE (s_expr) != SET)
            continue;

          if (sub_rtx == NULL)
            sub_rtx = &XVECEXP (PATTERN (def_insn), 0, i);
          else
            {
              /* PARALLEL with multiple SETs. */
              return false;
            }
        }
    }
  else if (code == SET)
    {
      sub_rtx = &PATTERN (def_insn);
    }
  else
    {
      /* It is not a PARALLEL or a SET, what could it be ? */
      return false;
    }

  gcc_assert (sub_rtx != NULL);

  if (GET_CODE (SET_DEST (*sub_rtx)) == REG
      && GET_MODE (SET_DEST (*sub_rtx)) == SImode)
    {
      setreg = get_reg_di (SET_DEST (*sub_rtx));
      if (!combine_set_zero_extend (def_insn, sub_rtx, setreg))
        {
          return false;
        }
      else
        {
          return true;
        }
    }
  else
    {
      return false;
    }
  return true;
}

/* This function goes through all reaching defs of the source
   of the zero extension instruction (zero_extend_insn) and
   tries to combine the zero extension with the definition
   instruction.  The changes are made as a group so that even
   if one definition cannot be merged, all reaching definitions
   end up not being merged. When a conditional copy is encountered,
   merging is attempted transitively on its definitions.  It returns
   true upon success and false upon failure. */

static bool
combine_reaching_defs (rtx zero_extend_insn, rtx set_pat)
{
  rtx newreg = NULL_RTX;
  rtx srcreg, def_insn;
  bool merge_successful = true;
  int i;
  int defs_ix;
  int outcome;

  /* To store the definitions that have been merged. */

  VEC (rtx, heap) *defs_list, *copies_list, *vec;
  enum insn_merge_code merge_code;

  srcreg = XEXP (SET_SRC (set_pat), 0);
  newreg = NULL_RTX;

  defs_list = VEC_alloc (rtx, heap, 8);
  copies_list = VEC_alloc (rtx, heap, 8);

  outcome = make_defs_and_copies_lists (zero_extend_insn,
                                        set_pat, &defs_list, &copies_list);

  /* outcome == 2 implies that all the definitions for this zero_extend were
     merged while previously when handling other zero_extends. */

  if (outcome == 2)
    {
      VEC_free (rtx, heap, defs_list);
      VEC_free (rtx, heap, copies_list);
      if (dump_file)
        fprintf (dump_file, "All definitions have been merged previously...\n");
      return true;
    }

  if (outcome == 0)
    {
      VEC_free (rtx, heap, defs_list);
      VEC_free (rtx, heap, copies_list);
      return false;
    }

  newreg = get_reg_di (srcreg);
  merge_successful = true;

  /* Go through the defs vector and try to merge all the definitions
     in this vector. */

  vec = VEC_alloc (rtx, heap, 8);
  for (defs_ix = 0; VEC_iterate (rtx, defs_list, defs_ix, def_insn); defs_ix++)
    {
      merge_code = get_insn_status (def_insn);
      gcc_assert (merge_code == MERGE_NOT_ATTEMPTED);

      if (merge_def_and_ze (def_insn))
        {
          VEC_safe_push (rtx, heap, vec, def_insn);
        }
      else
        {
          merge_successful = false;
          break;
        }
    }

  /* Now go through the conditional copies vector and try to merge all
     the copies in this vector.*/

  if (merge_successful)
    {
      for (i = 0; VEC_iterate (rtx, copies_list, i, def_insn); i++)
        {
          if (transform_ifelse (def_insn))
            {
              VEC_safe_push (rtx, heap, vec, def_insn);
            }
          else
            {
              merge_successful = false;
              break;
            }
        }
    }

  if (merge_successful)
    {
      /* Commit the changes here if possible */
      /* XXX : Now, it is an all or nothing scenario.  Even if one definition
         cannot be merged we totally bail.  In future, allow zero-extensions to
         be partially eliminated along those paths where the definitions could
         be merged.  */

      if (apply_change_group ())
        {
          if (dump_file)
            fprintf (dump_file, "All merges were successful ....\n");

          for (i = 0; VEC_iterate (rtx, vec, i, def_insn); i++)
            {
              set_insn_status (def_insn, MERGE_SUCCESS);
            }

          VEC_free (rtx, heap, vec);
          VEC_free (rtx, heap, defs_list);
          VEC_free (rtx, heap, copies_list);
          return true;
        }
      else
        {
          /* Changes need not be cancelled explicitly as apply_change_group ()
             does it.   Print list of definitions in the dump_file for debug
             purposes.  This zero-extension cannot be deleted. */

          if (dump_file)
            {
              for (i = 0; VEC_iterate (rtx, vec, i, def_insn); i++)
                {
                  fprintf (dump_file, " Ummergable definitions : \n");
                  print_rtl_single (dump_file, def_insn);
                }
            }
        }
    }
  else
    {
      /* Cancel any changes that have been made so far. */
      cancel_changes (0);
    }

  VEC_free (rtx, heap, vec);
  VEC_free (rtx, heap, defs_list);
  VEC_free (rtx, heap, copies_list);
  return false;
}

/* Goes through the instruction stream looking for zero-extends.  If the zero
   extension instruction has atleast one def it adds it to a list of possible
   candidates for deletion.  It returns the list of candidates. */
static VEC (rtx,heap)*
find_removable_zero_extends (void)
{
  VEC (rtx, heap) *zeinsn_list;
  basic_block curr_block;
  rtx curr_insn;
  rtx *set_insn;
  rtx which_reg;
  int type ;
  int has_defs;

  zeinsn_list = VEC_alloc (rtx, heap, 8);
  FOR_EACH_BB (curr_block)
    {
      FOR_BB_INSNS (curr_block, curr_insn)
        {
          if (!INSN_P (curr_insn))
            continue;

          type = for_each_rtx (&PATTERN (curr_insn),
                               is_set_with_extension_DI,
                               (void *)&set_insn);

          if (!type)
            continue;

          which_reg = XEXP (SET_SRC (*set_insn), 0);
          has_defs = get_defs (curr_insn, which_reg, NULL);
          if (has_defs)
            {
              VEC_safe_push (rtx, heap, zeinsn_list, curr_insn);
            }
          else if (dump_file)
            {
              fprintf (dump_file, "Cannot eliminate zero extension : \n");
              print_rtl_single (dump_file, curr_insn);
              fprintf (dump_file,
                       "This has no defs. Could be extending parameters.\n");
            }
        }
    }
  return zeinsn_list;
}

static unsigned int
find_and_remove_ze (void)
{
  rtx curr_insn = NULL_RTX;
  int i;
  int ix;
  long long num_realized = 0;
  long long num_ze_opportunities = 0;
  VEC (rtx, heap) *zeinsn_list;
  VEC (rtx, heap) *zeinsn_del_list;

  /* Construct DU chain to get all reaching definitions of each
     zero-extension instruction. */

  df_chain_add_problem (DF_UD_CHAIN + DF_DU_CHAIN);
  df_analyze ();

  max_insn_uid = get_max_uid ();

  is_insn_merge_attempted = XNEWVEC (enum insn_merge_code,
                                     sizeof (enum insn_merge_code)* max_insn_uid);

  for (i = 0; i < max_insn_uid; i++)
    {
      is_insn_merge_attempted[i] = MERGE_NOT_ATTEMPTED;
    }

  num_ze_opportunities = num_realized = 0;

  zeinsn_del_list = VEC_alloc (rtx, heap, 4);

  zeinsn_list = find_removable_zero_extends ();

  for (ix = 0; VEC_iterate (rtx, zeinsn_list, ix, curr_insn); ix++)
    {
      num_ze_opportunities++;
      /* Try to combine the zero-extends with the definition here. */

      if (dump_file)
        {
          fprintf (dump_file, "Trying to eliminate zero extension : \n");
          print_rtl_single (dump_file, curr_insn);
        }

      if (combine_reaching_defs (curr_insn, PATTERN (curr_insn)))
        {
          if (dump_file)
            fprintf (dump_file, "Eliminated the zero extension...\n");
          num_realized++;
          VEC_safe_push (rtx, heap, zeinsn_del_list, curr_insn);
        }
    }

  /* Delete all useless zero extensions here in one sweep. */
  for (ix = 0; VEC_iterate (rtx, zeinsn_del_list, ix, curr_insn); ix++)
    {
      delete_insn (curr_insn);
    }

  free (is_insn_merge_attempted);
  VEC_free (rtx, heap, zeinsn_list);
  VEC_free (rtx, heap, zeinsn_del_list);

  if (dump_file && num_ze_opportunities > 0)
    fprintf (dump_file, "\n %s : num_zee_opportunities = %lld "
                        "num_realized = %lld \n",
                        current_function_name (),
                        num_ze_opportunities, num_realized);

  df_finish_pass (false);
  return 0;
}

static unsigned int
rest_of_handle_zee (void)
{
  timevar_push (TV_ZEE);
  find_and_remove_ze ();
  timevar_pop (TV_ZEE);
  return 0;
}

static bool
gate_handle_zee (void)
{
  return (optimize > 0 && flag_zee);
}

struct rtl_opt_pass pass_implicit_zee =
{
 {
  RTL_PASS,
  "zee",                                /* name */
  gate_handle_zee,                      /* gate */
  rest_of_handle_zee,                   /* execute */
  NULL,                                 /* sub */
  NULL,                                 /* next */
  0,                                    /* static_pass_number */
  TV_ZEE,                               /* tv_id */
  0,                                    /* properties_required */
  0,                                    /* properties_provided */
  0,                                    /* properties_destroyed */
  0,                                    /* todo_flags_start */
  TODO_ggc_collect |
  TODO_dump_func |
  TODO_verify_rtl_sharing,              /* todo_flags_finish */
 }
};

