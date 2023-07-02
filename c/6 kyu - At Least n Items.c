#include <stdbool.h>
#include <stddef.h>

bool has_at_least(size_t n, const void *base, size_t nmemb, size_t size,
		  bool (*predicate)(const void *))
{
  if (!n) return true;

  size_t k = 0;
  for (size_t i = 0; i < nmemb; i++) {
    if (nmemb - i + k < n) return false;
    k += predicate(((char *) base) + i * size);
    if (k >= n) return true;
  }

  return false;
}

bool has_at_least_r(size_t n, const void *base, size_t nmemb, size_t size,
		    bool (*predicate)(const void *, void *arg), void *arg)
{
  if (!n) return true;
  
  size_t k = 0;
  for (size_t i = 0; i < nmemb; i++) {
    if (nmemb - i + k < n) return false;
    k += predicate(((char *) base) + i * size, arg);
    if (k >= n) return true;
  }
  
  return false;
}
