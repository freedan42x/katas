#include <stdio.h>
#include <string.h>

// returns a + b
static int addii(int a, int b)
{
  return a + b;
}

// concatenates a to the left of b, and returns b
static char *addis(int a, char *b)
{
  int K = strlen(b) + 32;
  char buf[K];
  sprintf(buf, "%d%s", a, b);
  strcpy(b, buf);
  return b;
}

// concatenates b to the right of a, and returns a
static char *addsi(char *a, int b)
{
  int K = strlen(a) + 32;
  char buf[K];
  sprintf(buf, "%s%d", a, b);
  strcpy(a, buf);
  return a;
}

// concatenates b to the right of a, and returns a
static char *addss(char *a, const char *b)
{
  return strcat(a, b);
}

#define add(x, y)				\
  _Generic(x,					\
	   int: _Generic(y,			\
			 int: addii,		\
			 char *: addis		\
			 ),			\
	   char *: _Generic(y,			\
			    int: addsi,		\
			    char *: addss	\
			    )			\
	   )(x, y)
