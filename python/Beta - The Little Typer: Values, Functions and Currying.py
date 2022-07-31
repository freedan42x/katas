TYPE_ID  = 0
TYPE_FUN = 1


class Id:
    def __init__(self, x):
        self.kind = TYPE_ID
        self.value = x

    def __str__(self):
        return self.value
        
    def __eq__(self, other):
        if other == None or other.kind != TYPE_ID: return False
        return self.value == other.value


class Fun:
    def __init__(self, x, y):
        self.kind = TYPE_FUN
        self.lhs = x
        self.rhs = y

    def __str__(self):
        l = str(self.lhs)
        if self.lhs.kind == TYPE_FUN:
            l = '(' + l + ')'

        r = str(self.rhs)
        return l + ' -> ' + r
        
    def __eq__(self, other):
        if other == None: return False
        return self.lhs == other.lhs and self.rhs == other.rhs


class Lit:
    def __init__(self, x):
        self.value = x

    def __str__(self):
        return str(self.value)

    def solve(self, ctx):
        tp = ctx.get(self.value)
        if tp == None:
            assert False

        return tp


class App:
    def __init__(self, fun, args):
        self.fun = Lit(fun) if isinstance(fun, str) else fun

        self.args = [Lit(arg) if isinstance(arg, str) else arg
                     for arg in args]

    def __str__(self):
        return str(self.fun) + '(' + ', '.join(map(str, self.args)) + ')'
        
    def solve(self, ctx):
        funtp = self.fun.solve(ctx)
        if funtp.kind != TYPE_FUN:
            assert False

        for arg in self.args:
            if funtp.lhs != arg.solve(ctx):
                assert False

            funtp = funtp.rhs

        return funtp


def parse_id(s, p):
    if s == '': return
    if not p(s[0]): return

    buf = s[0]
    i = 1
    while i < len(s):
        if s[i].isalnum():
            buf += s[i]
            i += 1
        else:
            break

    return (buf, i)

parse_type_id = lambda s: parse_id(s, lambda c: c.isupper())
parse_expr_id = lambda s: parse_id(s, lambda c: c.islower())


def parens(s):
    if s == '': return
    if s[0] != '(': return

    opn = 1
    i = 1
    while i < len(s):
        if s[i] == '(':
            opn += 1
        elif s[i] == ')':
            opn -= 1

        if opn == 0:
            break

        i += 1

    if opn > 0:
        assert False
    elif opn < 0:
        assert False
    else:
        return i


def parse_expr_part(s):
    s = s.strip()

    if (p := parse_expr_id(s)) != None:
        buf, j = p
        if j == len(s):
            return (buf, '')

        return (buf, s[j:])

    elif (j := parens(s)) != None:
        p = parse_expr_helper(s[1:j])
        return (p, s[j+1:])

    assert False


def parse_expr_helper(s):
    bufs = []
    while True:
        (buf, s) = parse_expr_part(s)
        bufs.append(buf)

        if s == '':
            if len(bufs) > 1:
                return App(bufs[0], bufs[1:])

            return bufs[0]

def parse_expr(s):
    e = parse_expr_helper(s)
    if isinstance(e, str):
        return Lit(e)

    return e


def parse_type(s):
    s = s.strip()
    if s == '': assert False

    if (i := parens(s)) != None:
        lhs = parse_type(s[1:i])
        j = i + 1
    else:
        if (p := parse_type_id(s)) == None:
            assert False

        lhs = Id(p[0])
        j = p[1]

    s = s[j:].strip()

    if s == '': return lhs

    if len(s) >= 2 and s[:2] == '->':
        return Fun(lhs, parse_type(s[2:]))

    assert False


def parse_ctx(s):
    ctx = {}
    for line in s.split('\n'):
        l = line.strip()
        if not l: continue

        name, tp = [x.strip() for x in line.split(':')]
        ctx[name] = parse_type(tp)

    return ctx


def infer_type(ctx_s, expr_s):
    ctx = parse_ctx(ctx_s)
    expr = parse_expr(expr_s)

    return str(expr.solve(ctx))
