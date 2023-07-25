#include <stdbool.h>
#include <stddef.h>

typedef bool (*predicate) (int);

int *take_while (size_t len_in, const int array[len_in], predicate p, size_t *len_out)
{
  size_t k = 0;
  while (k < len_in && p(array[k])) k++;
  *len_out = k;
  if (!k) return NULL;
  int *buf = malloc(sizeof(int) * k);
  memcpy(buf, array, sizeof(int) * k);
  return buf;
}
