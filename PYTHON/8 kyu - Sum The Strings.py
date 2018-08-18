def sum_str(a, b):
    if a == '' and b == '':
        return '0'
    elif a == '':
        return b
    elif b == '':
        return a
    else:
        sum = int(a) + int(b)
        return str(sum)
