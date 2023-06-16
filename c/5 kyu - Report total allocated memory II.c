#include <stdlib.h>

typedef struct node_t
{
  size_t sz;
  void *p;
  struct node_t *next;
} node_t;

size_t total_sz = 0;
node_t *allocs = NULL;

unsigned long long get_currently_allocated_size(void)
{
  return total_sz;
}

void *mem_alloc(size_t size)
{
  void *p = malloc(size);
  node_t *n = malloc(sizeof(*n));

  n->sz = size;
  n->p = p;
  n->next = allocs;
  allocs = n;
  total_sz += size;

  return p;
}

void mem_free(void *data)
{
  if (!data) return;
  
  node_t *cur = allocs;
  node_t *prev = NULL;
  while (cur && cur->p != data) {
    prev = cur;
    cur = cur->next;
  }

  if (!cur) return; // freeing unallocated
  
  if (!prev) { // needed is first on the list
    allocs = cur->next;
  } else {
    prev->next = cur->next;
  }

  total_sz -= cur->sz;
  free(data);
  free(cur);
}
