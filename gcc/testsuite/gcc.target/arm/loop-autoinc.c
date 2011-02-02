/* { dg-do compile } */
/* { dg-options "-mthumb -Os" } */
/* { dg-require-effective-target arm_thumb2_ok } */
/* { dg-final { scan-assembler "ldr\t.*\], #4" } } */

extern int x[];
extern void bar();
int foo ()
{
  int i;
  int sum = 0;
  for (i = 0; i < 100; i++) {
    sum += x[i];
    if (sum & 1)
      sum *= sum;
  }
  return sum;
}
