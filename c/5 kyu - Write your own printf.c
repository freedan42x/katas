#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define STR_INITIAL_CAP 256
typedef struct
{
  char *data;
  size_t count;
  size_t cap;
} str;

str str_make(void)
{
  str s;
  s.count = 0;
  s.cap = STR_INITIAL_CAP;
  s.data = malloc(s.cap);
  return s;
}

void str_reserve(str *s, size_t n)
{
  while (s->count + n > s->cap) {
    s->cap *= 2;
    s->data = realloc(s->data, s->cap);
  }
}

void str_add_char(str *s, char c)
{
  str_reserve(s, 1);
  s->data[s->count++] = c;
}

void str_add_cstr(str *s, const char *cstr)
{
  size_t k = strlen(cstr);
  str_reserve(s, k);
  memcpy(s->data + s->count, cstr, k);
  s->count += k;
}

void str_add_int(str *s, int x)
{
  str_reserve(s, 16);
  s->count += snprintf(s->data + s->count, 16, "%d", x);
}

char *str_to_cstr(str s)
{
  s.data[s.count] = 0;
  return s.data;
}

char *mr_asprintf(const char *fmt, ...)
{
  str s = str_make();
  
  va_list args;
  va_start(args, fmt);

  while (*fmt) {
    if (*fmt == '{') {
      char a = *(++fmt);
      if (a == '{') {
	str_add_char(&s, '{');
	fmt++;
	continue;
      }

      if (a == 'i') {
	str_add_int(&s, va_arg(args, int));
      } else if (a == 's') {
	str_add_cstr(&s, va_arg(args, const char *));
      } else {
	fprintf(stderr, "unknown specifier `%c`\n", a);
      }

      char b = *(++fmt);
      if (b != '}') {
	fprintf(stderr, "expected `}`");
      }
    } else {
      str_add_char(&s, *fmt);
    }

    fmt++;
  }
  
  va_end(args);
  
  return str_to_cstr(s);
}
