from functools import reduce

def disjunction(operands, is_exclusive):
  if is_exclusive:
    return reduce(bool.__xor__, operands)

  return any(operands)
