def fold_array(xs_, n):
    xs = xs_[:]
    while n != 0:
        for i in range(len(xs) // 2):
            xs[i] += xs.pop()
        n -= 1
    return xs
