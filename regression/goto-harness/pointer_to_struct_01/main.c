#include <assert.h>

struct S
{
  struct S *next;
};

struct S st;
struct S *p;

void initialize()
{
  st.next = &st;
  p = &st;
}

int main()
{
  //initialize();

  assert(p == &st);
  assert(p->next == &st);
}
