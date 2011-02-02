/* { dg-options "-O" } */
/* { dg-options "-O -m4" { target sh-*-* } } */

void foo (int *p)
{
  if (p)
    *p = 0;
}

int main()
{
  int x;
  foo (&x);
  return 0;
}

/* { dg-final { cleanup-coverage-files } } */
