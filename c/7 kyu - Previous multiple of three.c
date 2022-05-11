#include <sys/types.h>

ssize_t prev_mult_of_three(ssize_t n) {
  while (n % 3 != 0) {
    n /= 10;
  }
  return n ? n : -1;
}
