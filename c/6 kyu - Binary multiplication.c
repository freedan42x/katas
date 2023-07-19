#include <stddef.h>

void swap(unsigned *a, unsigned *b)
{
  unsigned t = *a;
  *a = *b;
  *b = t;
}

void bin_mul(unsigned m, unsigned n, unsigned *result, size_t *res_len)
{
  if (n > m) swap(&m, &n);

  size_t len = 0;
  while (m > 0) {
    if (m & 1) {
      result[len++] = n;
    }
    m /= 2;
    n *= 2;
  }
  *res_len = len;
  
  for (size_t i = 0; i < len / 2; i++) {
    swap(&result[i], &result[len - i - 1]);
  }
}
