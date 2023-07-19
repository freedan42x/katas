F = lambda x: lambda y: abs(x - y)
def getting_mad(arr):
    h, *t = arr
    if len(arr) == 2:
        return F(h)(t[0])
    return min(getting_mad(t), *map(F(h), t))
