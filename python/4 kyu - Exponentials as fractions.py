import math


class Fraction:
    def __init__(self, x):
        if isinstance(x, float):
            t = 10 ** len(str(x).split('.')[1])
            self.num = int(x * t)
            self.denum = t
        elif isinstance(x, list):
            self.num = x[0]
            self.denum = x[1]
        else:
            self.num = x
            self.denum = 1


    def simplify(self):
        t = math.gcd(self.num, self.denum)
        self.num //= t
        self.denum //= t


    def __add__(self, other):
        a, b, c, d = self.num, self.denum, other.num, other.denum
        f = Fraction([a * d + b * c, b * d])
        f.simplify()
        return f

    
    def __mul__(self, other):
        a, b, c, d = self.num, self.denum, other.num, other.denum
        f = Fraction([a * c, b * d])
        f.simplify()
        return f


    def __truediv__(self, other):
        f = self * Fraction([other.denum, other.num])
        f.simplify()
        return f
    

def expand(x, digit):
    r = Fraction(1)  
    x = Fraction(x)
    powx = x
    fact = 1
    k = 1
    while True:
        if len(str(r.num)) >= digit:
            return [r.num, r.denum]
        
        r += (powx / Fraction(fact))
        
        powx *= x
        fact *= (k + 1)
        k += 1
