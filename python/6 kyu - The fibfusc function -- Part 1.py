def fibfusc(n):
  if n == 0: return 1, 0
  if n == 1: return 0, 1
  x, y = fibfusc(n // 2)
  w = y*(2*x+3*y)
  if n % 2 == 0:
    return (x+y)*(x-y), w
  return -w, (x+2*y)*(x+4*y)
