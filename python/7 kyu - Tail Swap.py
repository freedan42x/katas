def tail_swap(strings):
    t = [s.split(':') for s in strings]
    return [t[0][0] + ':' + t[1][1], t[1][0] + ':' + t[0][1]]
