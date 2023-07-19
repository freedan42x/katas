#include <stdlib.h>

char *position(char alphabet)
{
  char *buf = NULL;
  asprintf(&buf, "Position of alphabet: %d", alphabet - 'a' + 1);
  return buf;
}
