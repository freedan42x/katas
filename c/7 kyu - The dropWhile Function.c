#include <stdbool.h>
#include <stdlib.h>

typedef bool (*Predicate)(const int*);

int *dropWhile(
  const int *values, 
  size_t     count,
  Predicate  pred, 
  size_t     *pResultCount)
{
  while (count && pred(values)) count--, values++;
  *pResultCount = count;
  int *rs = malloc(sizeof(int) * count);
  memcpy(rs, values, sizeof(int) * count);
  return count ? rs : NULL; // sadly malloc(0) does not return NULL
}
