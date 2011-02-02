/* { dg-do compile { target {{ i?86-*-* x86_64-*-* } && lp64 } } } */
/* { dg-options "-O2 -m64 -fdump-tree-ivopts" } */

#ifndef TYPE
#define TYPE char*
#endif

void foo (int i_width, TYPE dst, TYPE src1, TYPE src2)
{
      TYPE dstn= dst + i_width;
       for( ; dst < dstn; )
       {
           *dst++ = ( *src1++ + *src2++ + 1 ) >> 1;
       }
}

/* { dg-final { scan-tree-dump-times "PHI <ivtmp" 1 "ivopts"} } */
/* { dg-final { cleanup-tree-dump "ivopts" } } */
