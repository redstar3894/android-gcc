/* { dg-options "-O2" } */

unsigned test (unsigned a, unsigned b)
{
  return a / b;
}

int main()
{
  return test (6, 3) - 2;
}

/* { dg-final { cleanup-coverage-files } } */
