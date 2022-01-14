#include <stdint.h>

uint32_t ip_to_uint32(const char *ip)
{
  uint8_t b0, b1, b2, b3;
  sscanf(ip, "%hhu.%hhu.%hhu.%hhu", &b0, &b1, &b2, &b3); 
  return b3 | b2 << 8 | b1 << 16 | b0 << 24;
}
