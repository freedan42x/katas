#include <stdio.h>
#include <stdlib.h>

typedef struct {
  long long first;
  long long snd;
} Pair;

Pair** solEquaStr(long long n, int *length) {
  int k = 0;
  Pair **pairs = malloc(256 * sizeof(Pair *));
  for (long long i = 1; i * i <= n; i++) {
    if (n % i == 0 && (n / i + i) % (n & 1 ? 2 : 4) == 0) {
      pairs[k] = malloc(sizeof(Pair));
      pairs[k]->first = (n / i + i) / 2;
      pairs[k]->snd = pairs[k]->first / 2 - i / 2;
      k++;
    }
  }
  *length = k;
  return pairs;
}
