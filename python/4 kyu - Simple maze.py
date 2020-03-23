def player_ix(maze):
  x = 0
  for row in maze:
    if 'k' in row:
      return (x, row.index('k'))
    x += 1


def possible_ways(maze):
  (x, y) = player_ix(maze)
  return map(lambda p: p[0], filter(lambda p: p[1] != '#', [
      (lambda x, y: (x - 1, y), maze[x - 1][y]),
      (lambda x, y: (x + 1, y), maze[x + 1][y]),
      (lambda x, y: (x, y + 1), maze[x][y + 1]),
      (lambda x, y: (x, y - 1), maze[x][y - 1])
    ]))


def redraw(maze, new_player_ix):
  (x, y) = player_ix(maze)
  (new_x, new_y) = new_player_ix

  if maze[new_x][new_y] != ' ':
    return False

  maze[x] = list(maze[x])
  maze[x][y] = '#'
  maze[x] = ''.join(maze[x])

  maze[new_x] = list(maze[new_x])
  maze[new_x][new_y] = 'k'
  maze[new_x] = ''.join(maze[new_x])

  return maze


def has_exit(maze):
  if not maze:
    return False

  if '\n'.join(maze).count('k') > 1:
    0 / 0

  (x, y) = player_ix(maze)
  return y == len(maze[0]) - 1 or y == 0 or x == len(maze) - 1 or x == 0 or (
    any(has_exit(redraw(maze, f(x, y))) for f in possible_ways(maze)))
