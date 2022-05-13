from math import sin, factorial as fac

def taylors_sine_terms(x, error):
    ex = sin(x)
    i = 1
    cur = x
    while (abs(ex - cur) > error):
        k = 2 * i + 1
        cur += ((-1) ** i / fac(k)) * x ** k
        i += 1
    return i
    
