from math import gcd

def convertFracts(lst):
  lcm  = lambda x, y: x * y // gcd(x, y)
  lcmN = lambda x: x == [] or lcm(x[0], lcmN(x[1:]))
  n    = lcmN([x[1] for x in lst])
  return [[x * n // y, n] for x, y in lst]
