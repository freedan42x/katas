class INC_INT:
    def __init__(self, start, step):
        self.cur = 1 if start is None else start
        self.step = 1 if step is None else step

    def __next__(self):
        c = self.cur
        self.cur += self.step
        return c


class INC_FLOAT:
    def __init__(self, start, step, prec=1):
        self.cur = 0.1 if start is None else start
        self.step = 0.1 if step is None else step
        self.prec = prec

    def __next__(self):
        c = self.cur
        self.cur += self.step
        return c


class INTERVAL:
    def __init__(self, first, last):
        self.first = 1 if first is None else first
        self.last = self.first if last is None else last
        self.cur = self.first

    def __next__(self):
        if self.cur > self.last:
            self.cur = self.first
    
        c = self.cur
        self.cur += 1
        return c


class PERIODIC:
    def __init__(self, start, n):
        self.cur = 1 if start is None else start
        self.n = 1 if n is None else n
        self.times_called = 0

    def __next__(self):
        if self.times_called >= self.n:
            self.cur += 1
            self.times_called = 1
            return self.cur

        self.times_called += 1
        return self.cur


def get_token(s):
    name, *xy = s.replace(' ', '').split('=')
    x = None
    y = None
    if xy:
        xy = xy[0].split(',')
        x, *yarr = xy

        if yarr:
            assert len(yarr) == 1, 'excessive elements'
            y = yarr[0]

    if name == 'INC_FLOAT':
        ws = [len(str(a).split('.')[1]) for a in (x, y) if a is not None]
        p = max(*ws) if len(ws) == 2 else ws[0] if ws else 1
        prec = f', {p}'
    else:
        prec = ''

    return eval(f'{name}({x}, {y}{prec})')


class string_generator:
    def __init__(self, pattern):
        pattern = pattern.replace('{', '{{').replace('}', '}}')
        self.fmt = ''
        self.tokens = []

        buf = ''
        i = 0
        while i < len(pattern):
            if pattern[i] == '[':
                if buf:
                    self.fmt += buf
                    buf = ''

                j = pattern[i+1:].find(']')
                assert j != -1 and 'Unclosed `[`'
                t = get_token(pattern[i+1:i+j+1])
                self.tokens.append(t)
                if isinstance(t, INC_FLOAT):
                    self.fmt += '{:.' + str(t.prec) + 'f}'
                else:
                    self.fmt += '{}'
                i += j + 2
            else:
                buf += pattern[i]
                i += 1

        if buf: self.fmt += buf


    def __next__(self):
        return self.fmt.format(*[next(t) for t in self.tokens])
