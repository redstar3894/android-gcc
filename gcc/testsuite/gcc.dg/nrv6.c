/* Verify that changing to -O0 after a candidate for NRV optimization
   does not cause ICE.  */
/* { dg-do compile } */
/* { dg-options "-O2" } */

struct A {
  int i;
};

struct A foo (int i)
{
  struct A a;
  a.i  = i;
  return a;
}

#pragma GCC optimize("-O0")

int test(void)
{
  return 0;
}
