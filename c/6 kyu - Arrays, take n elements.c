#include <stddef.h>
#include <stdlib.h>
#include <string.h>

int *ary_take(const int *ary, size_t ary_size, size_t n, size_t *res_size)
{
  if (!n) {
    return NULL;
  }

  int k = n >= ary_size ? ary_size : n;
  *res_size = k;
  int *r = malloc(sizeof(int) * k);
  memcpy(r, ary, sizeof(int) * k);
  
  return r;
}
