#include <assert.h>

void store(int *px, int *py)
{
  *py = *px;
  __atomic_thread_fence(py);
}

void load(int *py, int *px)
{ 
  *px = *py;
  __atomic_thread_fence(py);
}

int main()
{
  int v, x, x_before;
  x_before = x;

  __atomic_store(&x, &x_before, 0);

  __atomic_load(&x_before, &x, 0);
  assert(x == x_before);
  return 0;
}
