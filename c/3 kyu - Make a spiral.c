#include <string.h>

typedef struct
{
  int x, y;
} V2;

void spiralize(unsigned n, int spiral[n][n])
{
  memset(&spiral[0][0], 0, sizeof(unsigned) * n * n);

  V2 dirs[4] = { {1, 0}, {0, 1}, {-1, 0}, {0, -1} };
  int dir_ix = 0;

  unsigned y = 0;
  unsigned x = 0;

  unsigned k = 0;
  while (k < n) {
    int ny = y + dirs[dir_ix].y;
    int nx = x + dirs[dir_ix].x;

    if (ny < 0 || ny >= (int) n || nx < 0 || nx >= (int) n) {
      dir_ix = (dir_ix + 1) % 4;
      k++;
      continue;
    }

    if (spiral[ny][nx]) {
      y -= dirs[dir_ix].y;
      x -= dirs[dir_ix].x;
      dir_ix = (dir_ix + 1) % 4;
      k++;
    } else {
      spiral[y][x] = 1;
      y = ny;
      x = nx;
    }
  }
}
