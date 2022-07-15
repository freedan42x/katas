def luck_check(s):
    if not s.isnumeric():
        raise ">_<"
    
    n = len(s)
    l = sum(map(int, s[:n//2]))
    r = sum(map(int, s[n//2+n%2:]))

    return l == r
