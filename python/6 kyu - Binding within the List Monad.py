bind = lambda xs, f: f(xs[0]) + bind(xs[1:], f) if xs else []
