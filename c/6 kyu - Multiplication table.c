#include <stdlib.h>

int **multiplication_table(int n) {
  int **table = malloc(sizeof(int *) * n);
  for (int i = 0; i < n; i++) {
    table[i] = malloc(sizeof(int) * n);
    for (int j = 0; j < n; j++) {
      table[i][j] = (i + 1) * (j + 1);
    }
  }
  return table;
}
