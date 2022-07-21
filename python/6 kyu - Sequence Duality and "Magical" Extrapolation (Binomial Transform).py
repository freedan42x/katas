import math

def delta(seq):
    r = []

    for i in range(len(seq) - 1):
        r.append(seq[i] - seq[i + 1])

    return r

def dual_seq(seq):
    r = []

    for n in range(len(seq)):
        s = 0

        for k in range(n + 1):
            s += (-1)**k * math.comb(n, k) * seq[k]

        r.append(s)

    return r

def extra_pol(seq, n):
    return dual_seq(dual_seq(seq) + [0] * n)
