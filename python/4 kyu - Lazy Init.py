def LazyInit(clsname, bases, attrs):
    if i := attrs.get('__init__'):
        fargs = i.__code__.co_varnames[1:]

        def f(self, *args):
            assert len(args) == len(fargs)
            for (arg, argname) in zip(args, fargs):
                setattr(self, argname, arg)

        attrs['__init__'] = f

    return type(clsname, bases, attrs)
