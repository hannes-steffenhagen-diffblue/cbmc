#include <assert.h>

int x;
int *p;

//not run here: it's what the snapshot should contain
void initialize()
{
  x = 3;
  p = &x;
}

int main()
{
  //  initialize();
  assert(*p == x);
}
