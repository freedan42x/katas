import re
import operator


class Parser:
    def __init__(self, s):
        self.s = s.replace(' ', '')
        self.ops_table = {
            '+': operator.add,
            '-': operator.sub,
            '*': operator.mul,
            '/': operator.truediv
        }

    def chop_num(self):
        buf = ''
        dot = False

        i = 0
        while i < len(self.s):
            if self.s[i].isdigit():
                i += 1
            elif self.s[i] == '.':
                if dot: return
                dot = True
                i += 1
            else: break

        if not i: return

        buf = self.s[:i]
        self.s = self.s[i:]

        return float(buf) if dot else int(buf)


    def chop_op(self):
        if self.s and (op := self.ops_table.get(self.s[0])):
            self.s = self.s[1:]
            return op

        return


    def parse_simple(self):
        if (result := self.chop_num()) is None:
            return result

        while self.s:
            if (op := self.chop_op()) is None:
                return
    
            if (x := self.chop_num()) is None:
                return

            if op == operator.truediv and x == 0:
                return

            result = op(result, x)

        return result


def calculate(s):
    if type(s) != str: return False

    for pat in re.split('\+|\-', s):
        result = Parser(pat).parse_simple()
        if result is None:
            return False

        rs = "%.32f" % result if type(result) == float else str(result)
        s = s.replace(pat, rs)

    if (r := Parser(s).parse_simple()) is None:
        return False

    return r
