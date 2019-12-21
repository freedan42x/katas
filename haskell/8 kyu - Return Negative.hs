module Codewars.Kata.Negative where

makeNegative :: (Num a, Ord a) => a -> a
makeNegative n
  | n > 0 = negate n
  | otherwise = n
