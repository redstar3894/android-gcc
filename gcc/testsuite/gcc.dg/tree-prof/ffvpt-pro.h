#include <math.h>

double d = VAL;
double s = 0.0;

int main (void)
{
  int i;
  for (i = 0; i < 1000; i++)
    {
      s += exp(d);
      s += pow(d, d);
      s += log(d);
      s += sqrt(d);
    }
  return 0;
}
