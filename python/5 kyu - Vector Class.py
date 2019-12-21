from math import sqrt
import numpy as np

class Vector:
    def __init__(self, *l):
      l = l[0] if len(l) is 1 else l
      self.x, self.y, self.z = l
      self.magnitude = sqrt(self.x ** 2 + self.y ** 2 + self.z ** 2)
      
    def to_tuple(self):
      return (self.x, self.y, self.z)
      
    def cross(self, other):
      return Vector(np.cross(list(self), list(other)))
      
    def dot(self, other):
      return self.x * other.x + self.y * other.y + self.z * other.z
    
    def __getitem__(self, item):
      return list(self)[item]
      
    def __iter__(self):
      return iter(self.to_tuple())
    
    def __eq__(self, other):
      return list(self) == list(other)
    
    def __add__(self, other):
      return Vector(self.x + other.x, self.y + other.y, self.z + other.z)
      
    def __sub__(self, other):
      return Vector(self.x - other.x, self.y - other.y, self.z - other.z)
      
    def __repr__(self):
      return '<%d, %d, %d>' % self.to_tuple()
