import re

def my_very_own_split(string, sep=None):
    if sep == '':
        raise ValueError('empty separator')
        
    if sep is None:
        sep = ' '
        string = re.sub(r'\s+', ' ', string)
    
    ixs = []
    ix = string.find(sep)
    while ix != -1:
        ixs.append(ix)
        ix = string.find(sep, len(sep) + ix)

    if not ixs:
        yield string
        return
        
    yield string[:ixs[0]]
    for i in range(len(ixs)):
        if i + 1 == len(ixs):
            yield string[ixs[i]+len(sep):len(string)]
        else:
            yield string[ixs[i]+len(sep):ixs[i + 1]]
