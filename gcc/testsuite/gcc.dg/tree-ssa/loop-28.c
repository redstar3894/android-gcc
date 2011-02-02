/* { dg-do compile { target i?86-*-* x86_64-*-* } } */
/* { dg-require-effective-target ilp32 } */
/* { dg-options "-O2 -fprefetch-loop-arrays -march=athlon -fdump-tree-final_cleanup -fdump-tree-aprefetch --param max-unrolled-insns=1000" } */

char x[100000];

void foo(int n)
{
  int i;

  for (i = 0; i < n; i++)
    x[i] = (char) i;
}

/* This loop would not be prefetched as the hardware sequential
prefetcher already prefetches it. */

/* { dg-final { scan-tree-dump-times "MEM" 1 "final_cleanup" } } */

/* There should be no i_a = i_b assignments.  */
/* { dg-final { scan-tree-dump-times "i_.*= i_\[0-9\]*;" 0 "aprefetch" } } */

/* { dg-final { cleanup-tree-dump "final_cleanup" } } */
/* { dg-final { cleanup-tree-dump "aprefetch" } } */
