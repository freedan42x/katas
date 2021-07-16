#include <stdlib.h>
#include <string.h>
#include <math.h>

char *binary_to_string(const char *binary)
{
  int len = strlen(binary);
  char *result = malloc(sizeof(char) * (1 + len / 8));
  char temp = 0;
  for (int i = 1; i <= len; i++)
  {
    if (binary[i - 1] == '1')
    {
      temp += pow(2, 7 - (i - 1) % 8);
    }
    if (i % 8 == 0)
    {
      result[i / 8 - 1] = temp;
      temp = 0;
    }
  }
  result[len / 8] = '\0';
  return result;
}
