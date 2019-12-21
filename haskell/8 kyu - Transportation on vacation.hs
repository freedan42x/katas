module Codewars.G964.Rentalcarcost where

rentalCarCost :: Int -> Int
rentalCarCost d
  | d > 2 && d < 7 = d * 40 - 20
  | d > 6          = d * 40 - 50
  | otherwise      = d * 40
