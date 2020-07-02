def sierpinski(n):
  if n == 0:
    return 'L'

  s = sierpinski(n - 1)
  l = s.split('\n')
  for i in range(2 ** n // 2):
    s += '\n' + l[i] + ' ' * (2 ** n - i * 2 - 1) + l[i]

  return s
