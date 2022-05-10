#include <stdlib.h>

typedef struct node_t {
  void *data;
  struct node_t *next;
} Node;

int length(const Node *head)
{
  if (head == NULL) return 0;
  return 1 + length(head->next);
}
