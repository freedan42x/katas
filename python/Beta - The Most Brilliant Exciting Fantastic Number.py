words = 'brilliant exciting fantastic virtuous heart-warming tear-jerking beautiful exhilarating emotional inspiring'.split()
def describe_num(n):
    s = 'The most'
    for i, w in enumerate(words):
        if n % (i + 1) == 0:
            s += ' ' + w
    return s + ' number is %d!' % n
