from operator import add, sub, mul, truediv


def tokenize(expr):
  result = []
  i = 0
  while i < len(expr):
    c = expr[i]
    if c == ' ':
      i += 1
      continue
    if c == '+':
      result.append('Plus')
      i += 1
    elif c == '-':
      result.append('Minus')
      i += 1
    elif c == '*':
      result.append('Mult')
      i += 1
    elif c == '/':
      result.append('Div')
      i += 1
    elif c == '(':
      result.append('OpenParen')
      i += 1
    elif c == ')':
      result.append('ClosedParen')
      i += 1
    else:
      num = ''
      while i < len(expr):
        c = expr[i]
        if c.isdigit() or c == '.':
          num += c
        else:
          break
        i += 1
      result.append(float(num))
  return result


ops = {
  'Plus': add,
  'Minus': sub,
  'Mult': mul,
  'Div': truediv
}


def parse_simple(tokens):
  if len(tokens) == 1:
    return tokens[0]

  i = 0
  while i < len(tokens):
    token = tokens[i]
    if token in ['Mult', 'Div']:
      new_tokens = \
          tokens[:i-1] \
        + [ops[token](tokens[i-1], tokens[i+1])] \
        + tokens[i+2:]
      return parse_simple(new_tokens)
    i += 1

  new_tokens = \
      [ops[tokens[1]](tokens[0], tokens[2])] \
    + tokens[3:]
  return parse_simple(new_tokens)


def parse(tokens):
  i = 0
  open_paren_ix = -1
  while i < len(tokens):
    token = tokens[i]
    if token == 'OpenParen':
      open_paren_ix = i
    elif token == 'ClosedParen':
      new_tokens = \
          tokens[:open_paren_ix] \
        + [parse_simple(tokens[open_paren_ix+1:i])] \
        + tokens[i+1:]
      return parse(new_tokens)
    i += 1
  return parse_simple(tokens)


class Calculator:
  def evaluate(self, expr):
    return parse(tokenize(expr))
