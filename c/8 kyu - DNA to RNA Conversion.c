#include <stdlib.h>
#include <string.h>

char *dna_to_rna(const char *dna)
{
  int len = strlen(dna);
  char *result = malloc(sizeof(char) * (len + 1));
  for (int i = 0; i < len; i++)
  {
    result[i] = dna[i] == 'T' ? 'U' : dna[i];
  }
  result[len] = '\0';
  return result;
}
