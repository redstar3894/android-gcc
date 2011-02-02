/* { dg-do compile } */
/* { dg-options "-O2 -fearly-stack-alloc -fstack-protector -fno-strict-aliasing -fdump-tree-stack-overlay" } */
void bar (char *);
void bar2 (int *);
void foo ()
  {
    {
      char a[100];
      bar (a);
    }
    {
      int a[100];
      bar2 (a);
    }
  }

/* { dg-final { scan-tree-dump "Number of partitions = 2" "stack-overlay" } } */
/* { dg-final { cleanup-tree-dump "stack-overlay" } } */
