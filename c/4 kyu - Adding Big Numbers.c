#include <stdlib.h>
#include <string.h>

char *add(const char *a, const char *b)
{
  const char *min_str = strlen(a) < strlen(b) ? a : b;
  const char *max_str = strlen(a) >= strlen(b) ? a : b;
  size_t min_len = strlen(min_str);
  size_t max_len = strlen(max_str);
  char *result = malloc(max_len + 2);
  strcpy(result + 1, max_str);
  result[0] = '0';
  
  for (int i = min_len - 1; i >= 0; i--) {
    size_t j = max_len - min_len + i + 1;
    size_t x = result[j] - '0';
    size_t y = min_str[i] - '0';
    result[j] = '0' + (x + y) % 10;

    if (x + y > 9) {
      size_t k = j - 1;
      while (result[k] == '9') {
        result[k] = '0';
        k--;
      }
      result[k]++;
    }
  }
  result[max_len + 1] = '\0';

  if (result[0] == '0') {
    memmove(result, result + 1, max_len);
    result[max_len] = '\0';
  }
  
  return result;
}
