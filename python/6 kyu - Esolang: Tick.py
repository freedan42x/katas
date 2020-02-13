class Stack:
  def __init__(self):
    self.pos = [0]
    self.neg = []
    self.ix = 0
    
  def mv_left(self):
    self.neg.insert(0, 0)
    self.ix -= 1
  
  def mv_right(self):
    self.pos.append(0)
    self.ix += 1

  def cells_ix(self):
    if self.ix < 0:
      return self.neg, len(self.neg) + self.ix
    return self.pos, self.ix

  def inc(self):
    cells, ix = self.cells_ix()
    cells[ix] = 0 if cells[ix] == 255 else cells[ix] + 1
    
  def asc(self):
    cells, ix = self.cells_ix()
    return chr(cells[ix])


def interpreter(prog):
  stack = Stack()
  result = ''
  for cmd in prog:
    if cmd == '>':
      stack.mv_right()
    elif cmd == '<':
      stack.mv_left()
    elif cmd == '+':
      stack.inc()
    elif cmd == '*':
      result += stack.asc()
  return result
