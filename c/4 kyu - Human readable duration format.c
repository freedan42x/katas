#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#define MINUTE 60
#define HOUR   (60 * MINUTE)
#define DAY    (24 * HOUR)
#define YEAR   (365 * DAY)
#define FORMAT(n, s) "%d " s"%s", n, n > 1 ? "s" : ""

char *formatDuration(int n)
{
  if (!n) return "now";
  
  char *result = malloc(64);
  char *buf[5];
  for (int i = 0; i < 5; i++) buf[i] = malloc(16);

  int y = n / YEAR;
  int d = n % YEAR / DAY;
  int h = n % DAY / HOUR;
  int m = n % HOUR / MINUTE;
  int s = n % MINUTE;

  size_t count = 0;
  if (y) sprintf(buf[count++], FORMAT(y, "year"));
  if (d) sprintf(buf[count++], FORMAT(d, "day"));
  if (h) sprintf(buf[count++], FORMAT(h, "hour"));
  if (m) sprintf(buf[count++], FORMAT(m, "minute"));
  if (s) sprintf(buf[count++], FORMAT(s, "second"));

  if (count == 1) return buf[0];

  for (size_t i = 0; i < count - 1; i++) {
    strcat(result, buf[i]);
    if (i == count - 2) {
      sprintf(result + strlen(result), " and %s", buf[i + 1]);
    } else {
      strcat(result, ", ");;
    }
  }
  
  return result;
}

int main(void)
{
  char *result = formatDuration(3662);
  printf("%s\n", result);
  free(result);
  
  return 0;
}
