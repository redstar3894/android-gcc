/* { dg-do compile { target i?86-*-* x86_64-*-* } } */
/* { dg-require-effective-target ilp32 } */
/* { dg-options "-O2 -fprefetch-loop-arrays -march=athlon -msse2 -mfpmath=sse --param simultaneous-prefetches=100 -fdump-tree-aprefetch-details" } */

int a[12000];

unsigned test(unsigned n)
{
  unsigned i, s = 0;

  /* Temporal prefetch should be issued here. */
  for (i = 0; i < 600; i++)
    s += a[i*20];

  return s;
}

/* { dg-final { scan-tree-dump-times "Issued prefetch" 1 "aprefetch" } } */

/* { dg-final { scan-assembler-times "prefetcht" 1 } } */

/* { dg-final { cleanup-tree-dump "aprefetch" } } */
