import re
import math

def expand(expr):
    a, var, b, n = re.match(r'\((\-?\d*)(\w)([\+\-]\d+)\)\^(\d+)', expr).groups()
    a = 1 if a == '' else -1 if a == '-' else int(a)
    b = int(b)
    n = int(n)

    s = ''
    for k in range(n + 1):
        p = n - k
        coeff = math.comb(n, k) * a ** p * b ** k

        if coeff == 0: continue

        if coeff == 1:
            coeff_s = '+1' if p == 0 else '+'
        elif coeff == -1:
            coeff_s = '-1' if p == 0 else '-'
        else:
            coeff_s = f'+{coeff}' if coeff > 0 else f'{coeff}'

        if p == 0:
            pow_s = ''
        elif p == 1:
            pow_s = var
        else:
            pow_s = f'{var}^{p}'
        
        s += coeff_s + pow_s

    return s[1:] if s[0] == '+' else s
