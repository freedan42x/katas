#include <stdio.h>

void check_bounds(int *n, int lower, int upper)
{
  if (*n < lower) *n = lower;
  else if (*n > upper) *n = upper;
}

int rgb(int r, int g, int b, char *output)
{
  check_bounds(&r, 0, 255);
  check_bounds(&g, 0, 255);
  check_bounds(&b, 0, 255);
  sprintf(output, "%06X", r << 16 | g << 8 | b);
  return 0; 
}
