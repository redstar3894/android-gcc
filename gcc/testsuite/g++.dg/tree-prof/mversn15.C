/* Make sure LIPO works correctly. dispatch is defined in mversn15a.C. It either
   calls foo or bar and both returns 1. So, the value of ret is always 1000.
   After cross-module inlining, main must return 0. */

/* { dg-additional-sources "mversn15a.C" } */
/* { dg-options "-O2 -fclone-hot-version-paths -fripa -fdump-tree-final_cleanup" } */

extern int foo ();
extern int bar ();
extern int dispatch ();

int
main ()
{
  int ret = 0;
  for (int i = 1; i <= 1000; i++)
   ret += dispatch ();
  return ret - 1000;
}

/* { dg-final-use { scan-tree-dump "main_clone" "final_cleanup" } } */
/* { dg-final-use { scan-tree-dump "return 0" "final_cleanup" } } */
/* { dg-final-use { cleanup-tree-dump "final_cleanup" } } */
