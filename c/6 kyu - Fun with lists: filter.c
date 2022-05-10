#include <stdbool.h>
#include <stdlib.h>

struct Node {
  struct Node *next;
  int data;
};

typedef bool (*predicate_func) (int);

/* return a fresh new list
   allocate each node on the heap, so that the list can be freed recursively
   do not mutate or re-use the input list
*/

struct Node *filter_list (const struct Node *list, predicate_func f)
{
  if (!list) return NULL;
  struct Node *prev = filter_list(list->next, f);
  if (f(list->data)) {
    struct Node *new = malloc(sizeof(struct Node));
    new->data = list->data;
    new->next = prev;
    return new;
  }
  return prev;
}
