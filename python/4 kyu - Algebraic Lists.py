class Cons:
  def __init__(self, head, tail):
    self.head = head
    self.tail = tail

  def to_array(self):
    return [self.head] + (self.tail.to_array() if self.tail else [])

  @classmethod
  def from_array(cls, arr):
    return cls(arr[0], cls.from_array(arr[1:])) if arr else None 

  def filter(self, f):
    tail = self.tail.filter(f) if self.tail else None
    return Cons(self.head, tail) if f(self.head) else tail

  def map(self, f):
    return Cons(f(self.head), self.tail.map(f) if self.tail else None)
