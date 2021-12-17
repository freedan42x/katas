#include <time.h>   // struct timespec
#include <stdlib.h> // div_t 

#define typeof(x) _Generic(x, \
  int: "int", \
  float: "float", \
  double: "double", \
  void *: "void*", \
  char *: "char*", \
  int *: "int*", \
  const int *: "const int*", \
  void (*) (void): "void (*) (void)", \
  struct timespec: "struct timespec", \
  div_t: "div_t", \
  default: "unknown type" \
)
