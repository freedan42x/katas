import math

def log(a, b):
    if a == 0: return None
    return [math.log(a**2 + b**2)/2, math.atan2(b, a)]
