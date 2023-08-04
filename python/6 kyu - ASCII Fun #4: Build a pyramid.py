def build_pyramid(s, n):
    r = ''
    for i in range(1, n + 1):
        if i > 1: r += '\n'
        r += ' ' * (len(s) * (n - i) // 2)
        for c in s:
            r += c * i
    return r
