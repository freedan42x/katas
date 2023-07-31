from time import time

def timer(limit):
    def d(fun):
        def w(*args, **kwargs):
            start = time()
            fun(*args, **kwargs)
            total = time() - start
            return total <= limit
        return w

    return d
