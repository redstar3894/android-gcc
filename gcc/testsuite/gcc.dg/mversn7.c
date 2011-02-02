/* This test checks if cloning and dispatching works correctly with
   a motivating example. The function problem calculates the sum of
   numbers from 1 to 10 in two different ways.  Hence, after cloning
   both clones should return 55, which means main returns 0 if function
   "problem" gets inlined.
   This example also shows the benefits of function
   unswitching.  Without cloning, the loop will be done. */

/* { dg-do run } */
/* { dg-options "-O2 -fclone-hot-version-paths -fdump-tree-final_cleanup" } */

int __attribute__ ((version_selector))
featureTest ()
{
  return 1;
}

int foo (int i)
{
  return i;
}

int bar (int i)
{
  return (11 - i);  
}

/* This calculates the sum of numbers from 1 to 10 in 2 different ways. */
int problem ()
{
  int ret = 0;
  int j = 1;
  for (j = 1; j<=10; j++)
    ret += __builtin_dispatch (featureTest, (void *)foo, (void *)bar, j);
  return ret;
}

int main ()
{
  return problem() - 55;
}


/* { dg-final { scan-tree-dump "return 55" "final_cleanup" } } */
/* { dg-final { cleanup-tree-dump "final_cleanup" } } */
