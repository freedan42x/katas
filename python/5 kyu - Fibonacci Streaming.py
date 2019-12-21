def all_fibonacci_numbers():
  yield 1
  m = 0
  n = 1
  while True:
    nxt = m + n
    m = n
    n = nxt     
    yield nxt
