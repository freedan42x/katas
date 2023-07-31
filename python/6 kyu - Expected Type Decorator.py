class UnexpectedTypeException(Exception): pass

def expected_type(types):
    def dec(fun):
        def wrapper(*args, **kwargs):
            r = fun(*args, **kwargs)
            if any(isinstance(r, t) for t in types):
                return r
            raise UnexpectedTypeException('(`O_o`)/')
        return wrapper
    return dec
