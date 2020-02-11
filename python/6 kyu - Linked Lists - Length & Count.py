class Node:
  def __init__(self, data, next=None):
    self.data = data
    self.next = next
    
def length(node):
  if node:
    return 1 + length(node.next)
  return 0
  
def count(node, data):
  if node:
    return (1 if node.data == data else 0) + count(node.next, data)
  return 0
