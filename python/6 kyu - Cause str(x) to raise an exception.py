def oops(_):
    raise Exception()
globals()['__builtins__']['str'] = oops
x = 1
