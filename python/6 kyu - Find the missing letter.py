def find_missing_letter(cs):
    k = ord(cs[0])
    for c in cs[1:]:
        t = ord(c)
        if t - k != 1:
            return chr(k + 1)
        k = t
