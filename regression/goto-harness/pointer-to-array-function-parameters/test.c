#include <assert.h>
#include <stdlib.h>

struct list
{
  struct list *next;
};

void do_array(struct list *list_array, int array_size)
{
  assert(list_array[0].next != NULL);
  assert(list_array[1].next != NULL);
  assert(list_array[0].next != list_array[1].next);
}
