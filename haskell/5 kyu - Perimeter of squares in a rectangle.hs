module Codewars.Kata.Perimeter where


perimeter :: Integer -> Integer
perimeter = (4 *) . helper 1 1 where
  helper a _ 0 = a
  helper a b n = a + helper b (a + b) (n - 1)
