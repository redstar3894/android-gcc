/* { dg-do compile { target {{ i?86-*-* x86_64-*-* } && lp64 } } } */
/* { dg-options "-O2 -m64 -fdump-tree-ivopts-details" } */
#include <stdlib.h>

int foo(const char* p, const char* p2, size_t N)
{
 const char* p_limit = p + N;
 int s = 0;
 while (p  <= p_limit - 16
        && *(long long*)p <*(long long*)p2)
 {
     p += 8;
     p2 += 8;
     s += (*p + *p2);
  }
  return s;
}
/* { dg-final { scan-tree-dump-times "Reordering" 1 "ivopts"} } */
/* { dg-final { scan-tree-dump-times "PHI <ivtmp" 1 "ivopts"} } */
/* { dg-final { cleanup-tree-dump "ivopts" } } */
