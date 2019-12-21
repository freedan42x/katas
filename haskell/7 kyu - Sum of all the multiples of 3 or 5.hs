module SumOfMultiples where

findSum n = sum [x | x <- [1..n], x `mod` 5 == 0 || x `mod` 3 == 0]
