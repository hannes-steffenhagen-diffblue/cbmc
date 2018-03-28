#include <assert.h>

#define ROUND(x) (int)((x)>0.0?(x)+0.5 : (x)-0.5)

const int C1 = ROUND(100./8.);
const int C2 = 100/8;
const int C3 = 13;
int g_in;
int g_out;

void func(void)
{
  if (g_in > C1)
    g_out = 1;    // (1)
  if (g_in > C2)
    g_out = 2;    // (2)
  if (g_in > C3)
    g_out = 3;    // (3)
}

void main(void)
{
  g_in = 0;
  g_in = 0;
  func();
  assert(!g_out);
}
