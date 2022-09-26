#include <string.h>
#include <stdlib.h>

int count_bits(int n)
{
  int b = 0;
  while (n) {
    b++;
    n >>= 1;
  }
  return b;
}

char *whitespace_number(int n)
{
  if (n == 0) {
    return strdup(" \n");
  }

  char *buf = malloc(3 + 8 * sizeof(int));

  buf[0] = n < 0 ? '\t' : ' ';
  n = n < 0 ? -n : n;

  int b = count_bits(n);
  for (int i = 1; i <= b; i++) {
    int z = (n & (1 << (b - i))) >> (b - i);
    buf[i] = z ? '\t' : ' ';
  }

  buf[b + 1] = '\n';
  buf[b + 2] = 0;

  return buf;
}
