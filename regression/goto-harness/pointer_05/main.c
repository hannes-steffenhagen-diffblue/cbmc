#include <assert.h>

int x;
int *p1;
int *p2;

void initialize()
{
  x = 3;
  p1 = &x;
  p2 = &x;
}

int main()
{
  //initialize();

  assert(*p1 == *p2);
}
