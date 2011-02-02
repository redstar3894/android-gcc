/* { dg-do compile { target {{ i?86-*-* x86_64-*-* } && lp64 } } } */
/* { dg-options "-O2 -m64 -fdump-tree-ivopts-details" } */
#include <stdlib.h>
int foo(const char* p, const char* p2, size_t N)
{
  const char* p_limit = p + N;
  while (p  <= p_limit - 16
        && *(long long*)p  <*(long long*)p2 )
  {
     p += 16;
     p2 += 16;
  }
  N = p_limit - p;
  return memcmp(p, p2, N);
}

/* { dg-final { scan-tree-dump-times "Sinking" 4 "ivopts"} } */
/* { dg-final { scan-tree-dump-times "Reordering" 1 "ivopts"} } */
/* { dg-final { cleanup-tree-dump "ivopts" } } */
