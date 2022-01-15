#include <stdio.h>
#include <string.h>

static const char *primitive_table[] = {
  [0] = "zero",
  [1] = "one",
  [2] = "two",
  [3] = "three",
  [4] = "four",
  [5] = "five",
  [6] = "six",
  [7] = "seven",
  [8] = "eight",
  [9] = "nine",
  [10] = "ten",
  [11] = "eleven",
  [12] = "twelve",
  [20] = "twenty"
};

const char *exception_table[] = {
  [2] = "twen",
  [3] = "thir",
  [4] = "for",
  [5] = "fif",
  [8] = "eigh"
};

char *number_to_words (unsigned n, char *num_string)
{
  if (n <= 12 || n == 20) {
    sprintf(num_string + strlen(num_string), "%s", primitive_table[n]);
  } else if (n > 12 && n < 20) {
    sprintf(num_string + strlen(num_string), "%steen", n != 14 && exception_table[n % 10] ? exception_table[n % 10] : primitive_table[n % 10]);
  } else if (n > 20 && n < 100) {
    sprintf(num_string + strlen(num_string), "%sty", exception_table[n / 10] ? exception_table[n / 10] : primitive_table[n / 10]);
    if (n % 10 != 0) {
      sprintf(num_string +strlen(num_string), "-%s", primitive_table[n % 10]);
    }
  } else if (n >= 100 && n < 1000) {
    sprintf(num_string + strlen(num_string), "%s hundred", primitive_table[n / 100]);
    if (n % 100 != 0) {
      strcat(num_string, " ");
      number_to_words(n % 100, num_string);
    }
  } else if (n >= 1000 && n < 1000000) {
    number_to_words(n / 1000, num_string);
    strcat(num_string, " thousand");
    if (n % 1000 != 0) {
      strcat(num_string, " ");
      number_to_words(n % 1000, num_string);
    }
  }
  
  return num_string;
}
