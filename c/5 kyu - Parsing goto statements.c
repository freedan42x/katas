#include <stdlib.h>

typedef struct {
  char *data;
  size_t size;
  size_t cap;
} str;

void str_add_char(str *s, char c)
{
  if (!s->data) {
    s->data = malloc(256);
    s->cap = 256;
  }

  if (s->size >= s->cap) {
    s->cap *= 2;
    s->data = realloc(s->data, s->cap);
  }

  s->data[s->size++] = c;
}

char *parse(const char *source)
{
  str s = {0};
  int goto_label = -1;

  while (*source) {
    char *end = NULL;
    int label = strtoul(source, &end, 10);
    if (end == source) {
      // goto
      source += 5;
      goto_label = strtoul(source, &end, 10);
      source = end + 1;
    } else {
      // label
      source = end + 1;
      if (goto_label == label) goto_label = -1;
      if (goto_label == -1) {
        if (s.size > 0) str_add_char(&s, ' ');
        while (*source != '\n') {
          str_add_char(&s, *source);
          source++;
  	}
      } else {
        while (*source != '\n') source++;
      }
      source++;
    }
  }
  str_add_char(&s, '\0');

  return s.data;
}
