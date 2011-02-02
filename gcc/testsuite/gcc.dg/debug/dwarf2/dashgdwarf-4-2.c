/* Verify that -gdwarf-2 overrides -gdwarf-4.  */

/* { dg-do compile */
/* { dg-options "-O0 -gdwarf-4 -gdwarf-2 -dA" } */
/* { dg-final { scan-assembler-not "DW_TAG_type_unit" } } */

struct bar {
  int i;
  int j;
};

void foo ()
{
  struct bar b = { 1, 2 };
}
