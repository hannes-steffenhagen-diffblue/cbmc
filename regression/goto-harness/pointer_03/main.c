#include <assert.h>

int x;
void *p;

void initialize()
{
  x = 3;
  p = (void *)&x;
}

int main()
{
  //initialize();
  assert(*(int *)p == 3);

  return 0;
}
