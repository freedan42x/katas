#include <stdio.h>

typedef struct {
  int r, g, b;
} rgb;

rgb hex_str_to_rgb(const char *hex_str) {
  int mask;
  sscanf(hex_str, "#%X", &mask);
  unsigned char *p = &mask;
  return (rgb) {p[2], p[1], p[0]};
}
