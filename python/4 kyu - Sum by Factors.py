def prime_factors(n):
    fs = []
    f = 2
    n = abs(n)
    while n > 1:
        if n % f == 0:     
            fs.append(f)
            n //= f
            while n % f == 0: n //= f
        else:
            f += 1
    return fs

def sum_for_list(lst):
    d = {}
    for x in lst:
        for p in prime_factors(x):
            d[p] = d.get(p, 0) + x

    return sorted([[k, v] for k, v in d.items()])
