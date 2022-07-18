def cache_collatz(n, cache):
    if n in cache: return cache[n]

    if n == 1:
        cache[1] = 1
        return 1
    
    if n & 1:
        cache[n] = 1 + cache_collatz(3 * n + 1, cache)
    else:
        cache[n] = 1 + cache_collatz(n // 2, cache)

    return cache[n]

def max_collatz_length(n):
    if type(n) != int or n < 1: return []
    
    cache = {}
    for i in range(1, n + 1):
        cache_collatz(i, cache)

    k = max(cache, key=cache.get)
    return [k, cache[k]]
