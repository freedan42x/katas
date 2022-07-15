module Codewars.Kata.FizzledCalculator where

import Prelude hiding ((*), (/), product)


-- | Should return True if x * y < z, otherwise False.
fizzledCalculator :: Double -> Double -> Double -> Bool
fizzledCalculator x y z
  | x == 0 || y == 0 = z > 0
  | x < 0 && y < 0 = fizzledCalculator (-x) (-y) z
  | (x < 0 || y < 0) && z >= 0 = True
  | x < 0 && z < 0 = not $ fizzledCalculator (-x) y (-z)
  | y < 0 && z < 0 = not $ fizzledCalculator x (-y) (-z)
  | z == 0 = False
  | otherwise = log x + log y < log z
