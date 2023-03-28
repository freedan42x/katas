import re


NODE_LIT = 0
NODE_OP = 1
NODE_IDENT = 2

OP_ADD = 0
OP_SUB = 1
OP_MUL = 2
OP_DIV = 3
OP_MOD = 4
OP_ASSIGN = 5
OP_NEGATE = 6

class Node:
    def __init__(self, tp, l=None, r=None):
        self.lhs = l
        self.rhs = r

        self.tp = tp
        self.lit = None
        self.op = None
        self.ident = None

    def __repr__(self):
        if self.tp == NODE_LIT:
            return f'Lit({self.lit})'

        if self.tp == NODE_OP:
            return f'Op({self.op}, {self.lhs}, {self.rhs})'

        if self.tp == NODE_IDENT:
            return f'Ident({self.ident})'

        raise Exception(f'unexpected node type {self.tp}')

def lit(x):
    node = Node(NODE_LIT)
    node.lit = x
    return node

def binary_op(op, lhs, rhs):
    node = Node(NODE_OP, lhs, rhs)
    node.op = op
    return node

def ident(s):
    node = Node(NODE_IDENT)
    node.ident = s
    return s

def negate(e):
    node = Node(NODE_OP, e)
    node.op = OP_NEGATE
    return node
    
class Result:
    def __init__(self, expr=None, rest=None):
        self.expr = expr
        self.rest = rest

    def __repr__(self):
        return f'Result< {self.expr} , rest={self.rest}>'

    def __bool__(self):
        return self.expr is not None


def expect(ts, c):
    return len(ts) > 0 and ts[0] == c


def expression(ts):
    if (lhs := muldiv(ts)):
        while (op := operator(lhs.rest)) and (op.expr in '+-') and (rhs := muldiv(op.rest)):
            lhs = binary_op({'+': OP_ADD, '-': OP_SUB}[op.expr], lhs.expr, rhs.expr)
            lhs = Result(lhs, rhs.rest)
        return lhs

    return Result()


def muldiv(ts):
    if (lhs := factor(ts)):
        while (op := operator(lhs.rest)) and (op.expr in '*/%') and (rhs := factor(op.rest)):
            lhs = binary_op({'*': OP_MUL, '/': OP_DIV, '%': OP_MOD}[op.expr], lhs.expr, rhs.expr)
            lhs = Result(lhs, rhs.rest)
        return lhs

    return Result()


def factor(ts):
    neg = False
    if expect(ts, '-'):
        neg = True
        ts = ts[1:]
    
    if (e := assignment(ts)) or (e := number(ts)) or (e := identifier(ts)):
        return Result(negate(e.expr), e.rest) if neg else e

    if expect(ts, '(') and (e := expression(ts[1:])) and expect(e.rest, ')'):
        return Result(negate(e.expr) if neg else e.expr, e.rest[1:])    

    return Result()


def assignment(ts):
    if (lhs := identifier(ts)) and expect(lhs.rest, '=') and (rhs := expression(lhs.rest[1:])):
        return Result(binary_op(OP_ASSIGN, lhs.expr, rhs.expr), rhs.rest)

    return Result()


def operator(ts):
    if len(ts) > 0 and ts[0] in '+-*/%':
        return Result(ts[0], ts[1:])

    return Result()


def identifier(ts):
    if len(ts) > 0 and all(c.isalpha() for c in ts[0]):
        node = Node(NODE_IDENT)
        node.ident = ts[0]
        return Result(node, ts[1:])

    return Result()


def number(ts):    
    if len(ts) > 0 and all(c.isdigit() for c in ts[0]):
        node = Node(NODE_LIT)
        node.lit = int(ts[0])
        return Result(node, ts[1:])

    return Result()


def tokenize(expression):
    if expression == "":
        return []

    regex = re.compile("\s*(=>|[-+*\/\%=\(\)]|[A-Za-z_][A-Za-z0-9_]*|[0-9]*\.?[0-9]+)\s*")
    tokens = regex.findall(expression)
    return [s for s in tokens if not s.isspace()]


ops = {
    OP_ADD: lambda x, y: x + y,
    OP_SUB: lambda x, y: x - y,
    OP_MUL: lambda x, y: x * y,
    OP_DIV: lambda x, y: x / y,
    OP_MOD: lambda x, y: x % y
}

def eval_node(node, vars):
    if node.tp == NODE_LIT:
        return node.lit

    if node.tp == NODE_OP:
        if node.op == OP_ASSIGN:
            x = eval_node(node.rhs, vars)
            vars[node.lhs.ident] = x
            return x

        if node.op == OP_NEGATE:
            return -eval_node(node.lhs, vars)

        if (f := ops.get(node.op)):
            return f(eval_node(node.lhs, vars), eval_node(node.rhs, vars))

        raise Exception(f'unknown op {node.op}')

    if node.tp == NODE_IDENT:
        if (x := vars.get(node.ident)):
            return x

        raise Exception(f'unknown identifier {node.ident}')

    raise Exception(f'unexpected node type {self.tp}')


class Interpreter:
    def __init__(self):
        self.vars = {}

    def input(self, expr):
        tokens = tokenize(expr)
        
        if not tokens:
            return ''
        
        result = expression(tokens)
        
        if result.rest:
            raise Exception('owo')

        return eval_node(result.expr, self.vars)
