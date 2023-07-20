class One:
    def eval(self):
        return 1


class Seq:
    def __init__(self, elems):
        self.elems = elems

    def eval(self):
        return sum(map(lambda e: e.eval(), self.elems))


class Nest:
    def __init__(self, value):
        self.value = value

    def eval(self):
        return 2 * self.value.eval()


def parse_one(s):
    if s[:2] == '()':
        return One(), s[2:]
    return None


def parse_nest(s):
    if s[:1] == '(':
        if r := parse_expr(s[1:]):
            if r[1][:1] == ')':
                return Nest(r[0]), r[1][1:]
    return None


def parse_seq(s):
    if (r := parse_nest(s)) or (r := parse_one(s)):
        es = [r[0]]
        s = r[1]
        while r := parse_expr(s):
            es.append(r[0])
            s = r[1]
        return Seq(es), s
    return None


def parse_expr(s):
    if (r := parse_seq(s)) or (r := parse_nest(s)) or (r := parse_one(s)):
        return r
    return None


def eval_parentheses(s):
    return parse_expr(s)[0].eval()
