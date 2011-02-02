/* This simple loops is perfectly prefetched by the hardware
   sequential prefetcher and thus there should be no software
   prefetches issued for it. */

/* { dg-do compile { target i?86-*-* x86_64-*-* } } */
/* { dg-require-effective-target ilp32 } */
/* { dg-options "-O2 -fprefetch-loop-arrays -march=athlon -msse2 -mfpmath=sse -fdump-tree-aprefetch-details" } */

#define N 1000000

double a[N];

double test(void)
{
  unsigned i;
  double sum = 0;

  for (i = 0; i < N; i += 2)
    sum += (a[i] * a[i+1]);

  return sum;
}

/* { dg-final { scan-assembler-times "prefetcht" 0 } } */
/* { dg-final { cleanup-tree-dump "aprefetch" } } */
