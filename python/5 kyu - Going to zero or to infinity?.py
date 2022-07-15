import math

def truncate(x, n):
    return math.floor(x * 10 ** n) / 10 ** n

def going(n):
    s, a = 0, 1

    for i in range(2, n + 1):
        s += a
        a *= i

    return truncate(1 + s / a, 6)
