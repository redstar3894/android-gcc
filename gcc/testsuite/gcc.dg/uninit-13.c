/* { dg-do compile } */
/* { dg-options "-O -Wuninitialized" } */

typedef _Complex float C;
C foo()
{
  C f;
  __imag__ f = 0;	/* { dg-warning "is used" "unconditional" { xfail arm*-*-* } } */
  return f;
}
/* { dg-excess-errors "fails on ARM." { target arm*-*-* } } */
