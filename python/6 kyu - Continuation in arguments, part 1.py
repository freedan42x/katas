def f(x, k):
  mult(x, 2, k)

def g(x, k):
  mult(10, x, lambda r: add(r, 1, k))

def main(k):
  g(2, lambda r: f(r, lambda r: show(r, k)))
