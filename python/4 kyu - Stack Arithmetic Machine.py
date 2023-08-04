from functools import reduce
import re
from operator import add, sub, mul, floordiv, and_, or_, xor


class Machine:    
    def __init__(self, cpu):
        self.cpu = cpu
        self.re = re.compile(r'^([a-z]+)(?:\s+([a-z]|\d+))?(?:\s*,\s*([a-z]))?$')
        self.arops = {
            'add': lambda xs: reduce(add, xs),
            'sub': lambda xs: reduce(sub, xs),
            'mul': lambda xs: reduce(mul, xs),
            'div': lambda xs: reduce(floordiv, xs),
            'and': lambda xs: reduce(and_, xs),
            'or':  lambda xs: reduce(or_, xs),
            'xor': lambda xs: reduce(xor, xs)
        }

    
    def reg(self, x):
        assert any(x == r for r in 'abcd'), 'not a register'
        return x


    def regint(self, x):
        if any(x == r for r in 'abcd'):
            return self.cpu.read_reg(x)
        
        if all(c.isdigit() for c in x):
            return int(x)
        
        assert False, 'not a register nor an immediate int'


    def pushr(self, regs):
        for r in regs:
            self.cpu.write_stack(self.cpu.read_reg(r))


    def popr(self, regs):
        for r in regs:
            self.cpu.write_reg(r, self.cpu.pop_stack())


    def execute(self, instr):
        s, x, y = self.re.match(instr).groups()

        if s == 'push':
            assert not y
            self.cpu.write_stack(self.regint(x))

        elif s == 'pop':
            assert not y
            t = self.cpu.pop_stack()
            if x: self.cpu.write_reg(self.reg(x), t)

        elif s == 'pushr':
            assert not x and not y
            self.pushr('abcd')

        elif s == 'pushrr':
            assert not x and not y
            self.pushr('dcba')

        elif s == 'popr':
            assert not x and not y
            self.popr('dcba')

        elif s == 'poprr':
            assert not x and not y
            self.popr('abcd')

        elif s == 'mov':
            self.cpu.write_reg(self.reg(y), self.regint(x))

        elif s in self.arops or s[:-1] in self.arops:
            if s[-1] == 'a':
                self.cpu.write_stack(self.cpu.read_reg('a'))
                s = s[:-1]

            vs = [self.cpu.pop_stack() for _ in range(self.regint(x))]
            self.cpu.write_reg(self.reg(y) if y else 'a', self.arops[s](vs))

        else:
            assert False, 'unknown instruction'
