def remove_parentheses(s):
  open, closed, ixs = 0, 0, []
  for i, c in enumerate(s):
    if c == '(':
      if open == closed:
        o_ix = i
      open += 1
    if c == ')':
      closed += 1
      if open == closed:
        ixs.append((o_ix, i))
  for i, j in ixs[::-1]:
    s = s[:i] + s[j+1:]
  return s
