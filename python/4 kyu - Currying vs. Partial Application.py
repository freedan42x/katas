import inspect
import copy

class curry_partial:
    def __new__(cls, f, *initial_args):
        self = super().__new__(cls)

        if type(f) == curry_partial:
            self.fun = f.fun
            self.supplied_args = f.supplied_args + list(initial_args)
            self.fun_args_len = f.fun_args_len
        elif not callable(f):
            return f
        else:
            self.fun = f
            self.supplied_args = list(initial_args)
            self.fun_args_len = len(inspect.signature(f).parameters)

        if len(self.supplied_args) >= self.fun_args_len:
            return self.fun(*self.supplied_args[:self.fun_args_len])

        return self

    def __call__(self, *args):
        s = super().__new__(curry_partial)
        s.fun = self.fun
        s.supplied_args = copy.deepcopy(self.supplied_args)
        s.fun_args_len = self.fun_args_len

        s.supplied_args.extend(args)

        if len(s.supplied_args) >= s.fun_args_len:
            return s.fun(*s.supplied_args[:s.fun_args_len])

        return s
