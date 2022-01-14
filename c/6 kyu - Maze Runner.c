#include <stddef.h>

enum {
  SAFE,
  WALL,
  START,
  FINISH
};

typedef struct
{
  int x, y;
} pos_t;

static pos_t dir_table[128] = {
  ['N'] = {0, -1},
  ['E'] = {1, 0},
  ['W'] = {-1, 0},
  ['S'] = {0, 1}
};

char *maze_runner(const int *maze, size_t n, const char *directions) {
  pos_t p;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      if (maze[i * n + j] == START) {
	      p.y = i, p.x = j;
      }
    }
  }

  while(*directions) {
    char dir = directions[0];

    p.x += dir_table[dir].x;
    p.y += dir_table[dir].y;
    
    if (maze[p.y * n + p.x] == WALL || p.x < 0 || p.y < 0 || p.x >= n || p.y >= n) {
      return "Dead";
    }
    if (maze[p.y * n + p.x] == FINISH) {
      return "Finish";
    }
    
    directions++;
  }

  return "Lost";
}
