/* { dg-do compile { target i?86-*-* x86_64-*-* } } */
/* { dg-require-effective-target ilp32 } */
/* { dg-options "-O2 -fprefetch-loop-arrays -march=athlon -msse2 -mfpmath=sse --param simultaneous-prefetches=100 -fdump-tree-aprefetch-details" } */

#define N 1000
#define K 900

double a[N][N];

double test(void)
{
  unsigned i, j;
  double sum = 0;

  /* Here, we should not use any prefetch instruction as this pattern
     is hardware prefetchable.  */
  for (i = 0; i < K; i++)
    for (j = 0; j < K; j++)
      sum += a[i][j];

  /* Here, we should not use prefetch instruction, since the value of
     a[i+10][j] is reused in L2 cache and the two inner loop strides
     a[i][j] and a[i+10] are hardware predictable. */
  for (i = 0; i < K; i++)
    for (j = 0; j < K; j++)
      sum += a[i][j] * a[i + 10][j];

  /* Here, we should not use any prefetch instruction, since the
    two independent strides a[i][j] and a[i+100][j] are hardware
    prefetchable in the inner-loop. */
  for (i = 0; i < K; i++)
    for (j = 0; j < K; j++)
      sum += a[i][j] * a[i + 100][j];

  /* Same as above. */
  for (i = 0; i < 100; i++)
    for (j = 0; j < 100; j++)
      sum += a[i][j] * a[i + 100][j];

  /* Temporal prefetches should be used here (even though the accesses to
     a[j][i] are independent, the same cache line is almost always hit
     every N iterations).  */
  for (i = 0; i < N; i++)
    for (j = 0; j < N; j++)
      sum += a[j][i];

  return sum;
}

/* { dg-final { scan-tree-dump-times "Issued prefetch" 1 "aprefetch" } } */

/* { dg-final { scan-assembler-times "prefetcht" 1 } } */

/* { dg-final { cleanup-tree-dump "aprefetch" } } */
