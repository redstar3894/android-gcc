/* { dg-do compile { target i?86-*-* x86_64-*-* } } */
/* { dg-require-effective-target ilp32 } */
/* { dg-options "-O2 -fprefetch-loop-arrays -march=athlon -msse2 -mfpmath=sse --param simultaneous-prefetches=100 --param max-unrolled-insns=1 -fdump-tree-aprefetch-details -fdump-tree-final_cleanup" } */

#define K 1000000
int a[K], b[K];

void test(int *p)
{
  unsigned i;

  /* Nontemporal store should be used neither for a nor for p, as we do not know
     whether they alias or not.  */
  for (i = 0; i < K; i++)
    {
      a[i] = 0;
      *p++ = 1;
    }
}

/* { dg-final { scan-tree-dump-times "nontemporal store" 0 "aprefetch" } } */

/* { dg-final { scan-assembler-times "prefetcht" 0 } } */
/* { dg-final { scan-assembler-times "prefetchnta" 0 } } */
/* { dg-final { scan-assembler-times "movnti" 0 } } */
/* { dg-final { scan-assembler-times "mfence" 0 } } */

/* { dg-final { cleanup-tree-dump "aprefetch" } } */
/* { dg-final { cleanup-tree-dump "final_cleanup" } } */
