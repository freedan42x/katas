def compare(a, b):

  if a and b:
    v = a.val == b.val
    L = compare(a.left, b.left)
    R = compare(a.right, b.right)
    return v and L and R
    
  return a == b
