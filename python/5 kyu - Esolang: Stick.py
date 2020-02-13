def interpreter(prog):
  stack, ix, result = [0], 0, ''
  while ix < len(prog):
    cmd = prog[ix]
    if cmd == '^':
      stack.pop()
    elif cmd == '!':
      stack.append(0)
    elif cmd == '+': 
      stack[-1] = (stack[-1] + 1) % 256
    elif cmd == '-':
      stack[-1] = (stack[-1] - 1) % 256 
    elif cmd == '*':
      result += chr(stack[-1])
    elif cmd == '[' and not stack[-1]:
      while prog[ix] != ']':
        ix += 1
    elif cmd == ']' and stack[-1]:
      while prog[ix] != '[':
        ix -= 1
    ix += 1
    
  return result
