#include <stddef.h>
#include <ctype.h>

size_t duplicate_count(const char *text) {
  int table[128] = {0};
  while (*text) {
    char c = tolower(text[0]);
    table[c]++;
    text++;
  }

  size_t count = 0;
  for (int i = 0; i < 128; i++) {
    count += table[i] > 1;
  }
  
  return count;
}
