def encoder(data):
    d = ['']
    r = ''

    t = ''
    j = 0
    for c in data:
        t += c

        try:
            j = d.index(t)
            match = True
        except ValueError:
            match = False
            d.append(t)
            t = ''
            r += str(j) + c

        if not match: j = 0

    if match: r += str(j)

    return r


def decoder(data):
    N = len(data)
    d = ['']
    r = ''

    i = 0
    while i < N:
        buf = ''
        while i < N and data[i].isdigit():
            buf += data[i]
            i += 1

        v = d[int(buf)] + (data[i] if i < N else '')
        r += v
        d.append(v)
        
        i += 1

    return r
