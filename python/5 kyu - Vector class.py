import math

class Vector:
    def __init__(self, arr):
        self.arr = arr

    def op(self, other, f):
        assert len(self.arr) == len(other.arr)
        return Vector([f(x, y) for x, y in zip(self.arr, other.arr)])
        
    def add(self, other):
        return self.op(other, lambda x, y: x + y)

    def subtract(self, other):
        return self.op(other, lambda x, y: x - y)

    def dot(self, other):
        return sum(self.op(other, lambda x, y: x * y).arr)

    def norm(self):
        return math.sqrt(sum(map(lambda x: x ** 2, self.arr)))

    def equals(self, other):
        return self.arr == other.arr

    def __str__(self):
        return '(' + ','.join(map(str, self.arr)) + ')'
