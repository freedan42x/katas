def simple_assembler(prog):
  line, ctx = 0, {}

  while line < len(prog):
    tokens = prog[line].split()

    try:
      cmd, a, b = tokens
    except ValueError:
      cmd, a = tokens

    if cmd == 'mov':
      if b.isalpha():
        ctx[a] = ctx[b]
      else:
        ctx[a] = int(b)
    elif cmd == 'inc':
      ctx[a] += 1
    elif cmd == 'dec':
      ctx[a] -= 1
    elif cmd == 'jnz':
      if (ctx[a] if a.isalpha() else int(a)):
        line += ctx[b] if b.isalpha() else int(b)
        continue
    line += 1
    
  return ctx
