from contextlib import suppress
from itertools import product, permutations

product_op = list(product(['+', '-', '*', '/'], repeat=3))

def parens(a, q1, b, q2, c, q3, d):
    return map(lambda lst: ''.join(map(str, lst)), [
        [a, q1, b, q2, c, q3, d],
        ['(', a, q1, b, ')', q2, c, q3, d],
        ['(', a, q1, b, q2, c, ')', q3, d],
        [a, q1, '(', b, q2, c, ')', q3, d],
        [a, q1, '(', b, q2, c, q3, d, ')'],
        [a, q1, b, q2, '(', c, q3, d, ')'],
        ['(', a, q1, b, ')', q2, '(', c, q3, d, ')']
    ])

def equal_to_24(a, b, c, d):
    perms_num = set(permutations([a, b, c, d]))
    for perm_num in perms_num:
        a, b, c, d = perm_num
        for prod_op in product_op:
            q1, q2, q3 = prod_op
            exprs = parens(a, q1, b, q2, c, q3, d)
            for expr in exprs:
                with suppress(ZeroDivisionError):
                    if eval(expr) == 24: return expr

    return 'It\'s not possible!'
