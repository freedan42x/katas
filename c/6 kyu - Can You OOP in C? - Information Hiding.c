#include <stdlib.h>

typedef struct _array_minmax_t {
  int min;
  int max;
} array_minmax_t;

array_minmax_t *array_minmax_create(unsigned int length, int *input_array) {
  array_minmax_t *arr = malloc(sizeof(array_minmax_t));

  arr->min = arr->max = input_array[0];
  for (unsigned int i = 1; i < length; i++)
  {
    if (input_array[i] > arr->max)
      arr->max = input_array[i];
    if (input_array[i] < arr->min)
      arr->min = input_array[i];
  }

  return arr;
}

void array_minmax_add(array_minmax_t *array, int number) {
  if (number < array->min)
    array->min = number;
  else if (number > array->max)
    array->max = number;
}

int array_minmax_get_min(array_minmax_t *array) {
  return array->min;
}

int array_minmax_get_max(array_minmax_t *array) {
  return array->max;
}

void array_minmax_destroy(array_minmax_t *array) {
  free(array);
}
