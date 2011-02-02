/* { dg-do compile } */
/* { dg-options "-O2 -fearly-stack-alloc -fno-strict-aliasing -fdump-tree-stack-overlay" } */
union U {
  int a;
  float b;
};
struct A {
  union U u1;
  char a[100];
};
void bar (struct A *);
void foo ()
  {
    {
      struct A a;
      bar (&a);
    }
    {
      struct A a;
      bar (&a);
    }
  }

/* { dg-final { scan-tree-dump "Number of partitions = 1" "stack-overlay" } } */
/* { dg-final { cleanup-tree-dump "stack-overlay" } } */
