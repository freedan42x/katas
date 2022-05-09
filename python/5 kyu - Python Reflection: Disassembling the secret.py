def find_the_secret(f):
    return f.__code__.co_consts[1]
