class Node:
  def __init__(self, data, next=None):
    self.data = data
    self.next = next

def append(xs, ys):
  return Node(xs.data, append(xs.next, ys)) if xs else ys
