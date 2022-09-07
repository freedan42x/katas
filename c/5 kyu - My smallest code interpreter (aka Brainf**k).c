#include <string.h>
#include <stdio.h>
#include <stdlib.h>

void brainfuck(const char *code, const char *input, char *output)
{
  unsigned char memory[1024 * 16] = {0};
  unsigned char *ptr = memory;
  int output_len = 0;
  int input_len = 0;

  int n = strlen(code);
  int i = 0;
  while (i < n) {
    switch (code[i]) {
    case '>':
      ptr++;
      i++;
      break;

    case '<':
      ptr--;
      i++;
      break;

    case '+':
      (*ptr)++;
      i++;
      break;

    case '-':
      (*ptr)--;
      i++;
      break;

    case '.':
      output[output_len++] = *ptr;
      i++;
      break;

    case ',':
      *ptr = input[input_len++];
      i++;
      break;

    case '[':
      if (*ptr == 0) {
	int open = 1;
	int j = i + 1;
	while (j < n) {
	  if (code[j] == ']') {
	    if (open == 1) {
	      i = j + 1;
	      break;
	    } else {
	      open--;
	    }
	  }

	  if (code[j] == '[') {
	    open++;
	  }

	  j++;
	}
	continue;
      }
      i++;
      break;

    case ']':
      if (*ptr != 0) {
	int closed = 1;
	int j = i - 1;
	while (j >= 0) {
	  if (code[j] == '[') {
	    if (closed == 1) {
	      i = j + 1;
	      break;
	    } else {
	      closed--;
	    }
	  }

	  if (code[j] == ']') {
	    closed++;
	  }

	  j--;
	}
	continue;
      }
      i++;
      break;

    default:
      fprintf(stderr, "Unknown command: %c\n", code[i]);
      exit(1);
    }
  }

  output[output_len] = 0;
}
