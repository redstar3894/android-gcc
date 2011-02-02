/* { dg-do compile } */
/* { dg-options "-O2 -fearly-stack-alloc -fno-strict-aliasing -fdump-tree-stack-overlay" } */
void bar( char *);
int foo()
{
  int i=0;
  {
    char a[8192];
    bar(a);
    i += a[0];
  }
  {
    char a[8192];
    char b[32];
    bar(a);
    i += a[0];
    bar(b);
    i += a[0];
  }
  return i;
}
/* { dg-final { scan-tree-dump "Number of partitions = 2" "stack-overlay" } } */
/* { dg-final { scan-tree-dump "size 8192" "stack-overlay" } } */
/* { dg-final { scan-tree-dump "size 32" "stack-overlay" } } */
