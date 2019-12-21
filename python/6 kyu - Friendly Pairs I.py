from math import gcd

divsum = lambda x: sum(filter(lambda y: x % y == 0, range(1, x // 2 + 1))) + x

def friendly_numbers(m, n):
    
    if divsum(m)/m == divsum(n)/n:
      return 'Friendly!'
      
    x = divsum(m)
    y = divsum(n)
    a = gcd(x, m)
    b = gcd(y, n)
    
    return f'{x // a}/{m // a} {y // b}/{n // b}'
