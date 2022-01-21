#include <stdio.h>
#include <stdlib.h>

int **matrix_multiplication(int **a, int **b, int n)
{
  int **result = malloc(sizeof(int *) * n);

  for (int i = 0; i < n; i++) {
    result[i] = malloc(sizeof(int) * n);
    for (int j = 0; j < n; j++) {
      int sum = 0;
      for (int k = 0; k < n; k++) {
	      sum += a[i][k] * b[k][j];
      }
      result[i][j] = sum;
    }
  }
  
  return result;
}
