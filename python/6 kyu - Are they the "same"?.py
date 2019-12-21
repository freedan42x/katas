comp = lambda a, b: False if a == None or b == None else all(x**2 == y or x == y for x, y in zip(sorted(a), sorted(b)))
