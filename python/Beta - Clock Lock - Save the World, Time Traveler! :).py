chars = '0123456789abcdef'

def measure(password):
    return timeit.timeit(lambda: clocklock.checkpwd(password), number=1)

def getpwd():
    password = ['f'] * 20
    for i in range(0, len(password)):
        rs = {}
        for c in chars:
            password[i] = c
            rs[c] = measure(password)
        password[i] = max(rs, key=rs.get)
    return ''.join(password)
