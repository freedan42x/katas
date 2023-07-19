class predicate:
    def __init__(self, fun):
        self.fun = fun

    def __call__(self, *args, **kwargs):
        return self.fun(*args, **kwargs)

    def __and__(self, other):
        def f(*args, **kwargs):
            return self.fun(*args, **kwargs) and other.fun(*args, **kwargs)
        return predicate(f)

    def __or__(self, other):
        def f(*args, **kwargs):
            return self.fun(*args, **kwargs) or other.fun(*args, **kwargs)
        return predicate(f)

    def __invert__(self):
        def f(*args, **kwargs):
            return not self.fun(*args, **kwargs)
        return predicate(f)
