table = [
    ('lava', 800),
    ('blaze rod', 120),
    ('coal', 80),
    ('wood', 15),
    ('stick', 1)
]

def calc_fuel(n):
    s = n * 11
    d = {}
    for k, v in table:
        if s >= v:
            d[k] = s // v
            s -= d[k] * v
        else:
            d[k] = 0
    return d
