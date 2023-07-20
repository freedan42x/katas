def rep_set(n):
    if n == 0: return []
    r = rep_set(n - 1)
    return r + [r]
