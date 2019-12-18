from math import gcd

class Fraction:

    def __init__(self, numerator, denominator):
        self.top = numerator
        self.bottom = denominator
    
    def __eq__(self, other):
        first_num = self.top * other.bottom
        second_num = other.top * self.bottom
        return first_num == second_num
        
    def __add__(self, other):
      t = gcd(self.bottom, other.bottom)
      first_num = self.bottom // t
      second_num = other.bottom // t
      top, bottom = (other.top * first_num + self.top * second_num, other.bottom * first_num)
      t = gcd(top, bottom)
      return Fraction(top // t, bottom // t)
      
    def __repr__(self):
      return '%d/%d' % (self.top, self.bottom)
