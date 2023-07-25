#include <inttypes.h>
#include <math.h>

typedef uint64_t u64;

u64 modpow (u64 base, u64 exponent, u64 modulo)
{
  u64 x = 1;
  base %= modulo;
  while (exponent > 0) {
    if (exponent & 1) {
      x = (x * base) % modulo;
    }
    base = (base * base) % modulo;
    exponent >>= 1;
  }
	return x;
}
