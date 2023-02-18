#include <inttypes.h>
#include <stdio.h>

void uint32_to_ip(uint32_t number, char *IPv4)
{
  int offset = 0;
  offset += sprintf(IPv4 + offset, "%d.", number >> 24 & 0xFF);
  offset += sprintf(IPv4 + offset, "%d.", number >> 16 & 0xFF);
  offset += sprintf(IPv4 + offset, "%d.", number >> 8 & 0xFF);
  offset += sprintf(IPv4 + offset, "%d", number & 0xFF);
  IPv4[offset] = 0;
}
