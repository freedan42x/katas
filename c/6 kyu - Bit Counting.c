#include <stddef.h>

size_t countBits(unsigned value)
{
  size_t s = 0;
  while (value) {
    s += value & 1;
    value >>= 1;
  }
  return s;
}
