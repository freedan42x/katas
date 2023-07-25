#include <stddef.h>

void transpose_matrix (
  size_t rows, size_t cols,
  const int matrix[rows][cols],
  int transpose[cols][rows])
{
  for (size_t row = 0; row < rows; row++) {
    for (size_t col = 0; col < cols; col++) {
      transpose[col][row] = matrix[row][col];
    }
  }
}
