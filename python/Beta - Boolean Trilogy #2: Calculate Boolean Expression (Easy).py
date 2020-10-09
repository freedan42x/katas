def calculate(expr, values):
  for k, v in values.items():
    expr = expr.replace(k, str(v))
  return eval(expr)
