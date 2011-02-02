/* { dg-do run { target x86_64-*-* i?86-*-* } } */
/* { dg-options "-save-temps -O2 -msse2" } */


#include <stdio.h>
#include <xmmintrin.h>
#include <emmintrin.h>
__m128i m;
__m128i m2;
__attribute__((noinline))  __m128i foo()
{
  __m128i  minus_1 = __extension__(__m128i)(__v4si){-1,-1,-1,-1};
  m = minus_1;
  return minus_1;
}


int main ()
{
    unsigned *p, *p2;
    p = (unsigned *)&m;
    p2 =(unsigned *)&m2;
    m2 = foo();

    if (p[0] != (unsigned)-1 
        || p[1] != (unsigned) -1
        || p[2] != (unsigned) -1
        || p[3] != (unsigned) -1)
      return 1;

    if (p2[0] != (unsigned)-1 
        || p2[1] != (unsigned) -1
        || p2[2] != (unsigned) -1
        || p2[3] != (unsigned) -1)
      return 2;
        
    return 0;
}

/* { dg-final { scan-assembler "pcmpeqd" } } */
/* { dg-final { cleanup-saved-temps } } */
