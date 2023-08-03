class Simplexer:
    def __init__(self, s):
        self.s = s
        self.i = 0
        self.tokens = []
        self.lex()


    def lex(self):
        fs = [self.string, self.keyword, self.boolean, self.identifier, self.whitespace, self.operator, self.integer]
        while self.i < len(self.s):
            for f in fs:
                if t := f():
                    self.tokens.append(t)
                    break
            else:
                assert False

        self.tokens = iter(self.tokens)


    def identifier(self):
        pred = lambda c: c.isalnum() or c in '_$'
        if pred(self.s[self.i]) and not self.s[self.i].isdigit():
            j = self.i + 1
            while j < len(self.s) and pred(self.s[j]):
                j += 1

            t = Token(self.s[self.i:j], 'identifier')
            self.i = j
            return t


    def string(self):
        j = self.i
        if self.s[j] == '"':
            j += 1
            while j < len(self.s):
                if self.s[j] == '"':
                    t = Token(self.s[self.i:j+1], 'string')
                    self.i = j + 1
                    return t
                j += 1


    def integer(self):
        j = self.i
        while j < len(self.s) and self.s[j].isdigit():
            j += 1

        if j > self.i:
            t = Token(self.s[self.i:j], 'integer')
            self.i = j
            return t


    def boolean(self):
        for b in 'true', 'false':
            if self.s[self.i:self.i+len(b)] == b:
                self.i += len(b)
                return Token(b, 'boolean')


    def keyword(self):
        for k in 'if', 'else', 'for', 'while', 'return', 'func', 'break':
            if self.s[self.i:self.i+len(k)] == k:
                self.i += len(k)
                return Token(k, 'keyword')


    def operator(self):
        for o in '+', '-', '*', '/', '%', '(', ')', '=':
            if self.s[self.i] == o:
                self.i += 1
                return Token(o, 'operator')


    def whitespace(self):
        j = self.i
        while j < len(self.s) and self.s[j].isspace():
            j += 1

        if j > self.i:
            t = Token(self.s[self.i:j], 'whitespace')
            self.i = j
            return t


    def __iter__(self):
        return self.tokens


    def __next__(self):
        return next(self.tokens)
