def parse (data):
    val = 0
    arr = []
    for s in data:
      if s == 'i':
        val += 1
      elif s == 'd':
        val -= 1
      elif s == 's':
        val *= val
      elif s == 'o':
        arr.append(val)
      else:
        continue
    return arr;
