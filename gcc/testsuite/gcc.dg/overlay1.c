/* Check that store sinking does not break stack overlay */
/* { dg-do run } */
/* { dg-options "-O2 -fearly-stack-alloc" } */

extern void abort (void);

struct a;

typedef void (*func_t)(struct a*);

struct a {
  func_t impl;
};

struct b {
  struct a base;
};

void
a_impl (struct a *const this)
{
  abort();
}

void
b_impl (struct a * const this)
{
}

void __attribute__((noinline))
a_interface (struct a * const this)
{
  this->impl(this);
}

int
main(int argc, char **argv)
{
  {
  struct b obj1;

L1:
    if (argc > 400)
      return 0;
    obj1.base.impl = b_impl;

L2:
    a_interface (&obj1.base);
    obj1.base.impl = b_impl;
    obj1.base.impl = a_impl;
    if (argc > 200)
      return 0;
  }
  {
  struct b obj2;
    obj2.base.impl = a_impl;

L3:
    obj2.base.impl = b_impl;
    if (argc > 100)
      return 0;

L4:
    a_interface (&obj2.base);
    obj2.base.impl = b_impl;
    obj2.base.impl = a_impl;
  }

  return 0;
}
