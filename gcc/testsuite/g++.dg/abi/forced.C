// This test only applies to glibc (NPTL) targets.
// { dg-do run { target *-*-linux* } }
// { dg-options "-pthread" }
// Does not work on a QEMU set-up because of the status wrapper.
//{ dg-require-effective-target unwrapped }

#include <pthread.h>
#include <cxxabi.h>
extern "C" int printf (const char *, ...);

int main()
{
  try
    {
      pthread_exit (0);
    }
  catch (abi::__forced_unwind &)
    {
      printf ("caught forced unwind\n");
      throw;
    }
  catch (...)
    {
      printf ("caught ...\n");
      return 1;
    }
}
