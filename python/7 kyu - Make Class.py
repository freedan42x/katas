def make_class(*ns):
  class C:
    def __init__(self, *vs):
      for (n, v) in zip(ns, vs):
        setattr(self, n, v)
  return C
