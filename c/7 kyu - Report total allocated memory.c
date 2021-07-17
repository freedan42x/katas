#include <stdlib.h>

unsigned long long SIZE = 0;

void *mem_alloc(size_t size)
{
  SIZE += size;
  
  return malloc(size);
}

unsigned long long report_total_allocated(void)
{
  return SIZE;
}
