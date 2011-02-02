/* { dg-do compile } */
/* { dg-options "-O2  -fdump-tree-optimized" } */
struct B {

  B();
  virtual int foo(void);
  int i;
  ~B() {}
};

struct D : public B{
  D(int i);
  int foo(void);
  ~D() {}
  int d;
};

 int _main(void)
 {
   D *d = new D('c');

   delete d;
   return 0;
 }
 
/* { dg-final { scan-tree-dump-times "vptr" 0 "optimized"} } */
/* { dg-final { cleanup-tree-dump "optimized" } } */
