#include <assert.h>
#include <stdlib.h>

struct list
{
  struct list *next;
};

void do_array(struct list *list_array1, struct list *list_array2 int array_size)
{
  assert(list_array1 != list_array2);

  assert(list_array1[0].next != NULL);
  assert(list_array1[1].next != NULL);
  assert(list_array1[0].next != list_array1[1].next);

  assert(list_array2[0].next != NULL);
  assert(list_array2[1].next != NULL);
  assert(list_array2[0].next != list_array2[1].next);
}
