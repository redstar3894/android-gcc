/* Call the caller of __builtin_dispatch indirectly.  Specify the
   feature test function as a function pointer.  Make sure cloning
   still happens. */

/* { dg-do run } */
/* { dg-options "-O2 -fclone-hot-version-paths -fdump-tree-final_cleanup" } */

int __attribute__ ((version_selector))
featureTest ()
{
  return 1;
}

int __attribute__ ((cold))
foo ()
{
  return 0;
}

int __attribute__ ((cold))
bar ()
{
  return 1;
}

int
dispatch ()
{
  int (*funcp)() = featureTest;
  int ret = __builtin_dispatch (funcp, (void *)foo, (void *)bar);
  return ret;
}

int main (int argc, char **argv)
{
  int (*ptr)() = dispatch;
  return (*ptr)();
}

/* { dg-final { scan-tree-dump "dispatchv_clone_0" "final_cleanup" } } */
/* { dg-final { scan-tree-dump "dispatchv_clone_1" "final_cleanup" } } */
/* { dg-final { scan-tree-dump "main_clone_0" "final_cleanup" } } */
/* { dg-final { scan-tree-dump "main_clone_1" "final_cleanup" } } */
/* { dg-final { cleanup-tree-dump "final_cleanup" } } */
