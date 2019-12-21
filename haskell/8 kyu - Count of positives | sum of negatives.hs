module Kata where

countPositivesSumNegatives :: Maybe [Int] -> [Int]
countPositivesSumNegatives Nothing = []
countPositivesSumNegatives (Just []) = []
countPositivesSumNegatives xs = [length (filter (> 0) a), sum (filter (< 0) a)] where
  a = concat xs
