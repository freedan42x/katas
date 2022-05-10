#include <stddef.h>

struct Node {
  struct Node *next;
  int data;
};

typedef int (*map_func) (int);

/* return a fresh new list
   allocate each node on the heap, so that the list can be freed recursively
   do not mutate or re-use the input list
*/

struct Node *map_list (const struct Node *list, map_func f)
{
  if (!list) return NULL;
  struct Node *new = malloc(sizeof(struct Node));
  new->data = f(list->data);
  new->next = map_list(list->next, f);
  return new;
}
