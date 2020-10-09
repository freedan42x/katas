from math import ceil

def what_century(year):
  r = ceil(int(year) / 100)
  e = r < 11 or r > 13 and {1: 'st', 2: 'nd', 3: 'rd'}.get(r % 10) or 'th'
  return str(r) + e
