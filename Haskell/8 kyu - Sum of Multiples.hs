module Kata where

sumMul :: Int -> Int -> Maybe Int
sumMul n m 
  | n >= m    = Nothing
  | otherwise = Just $ sum [n, n + n..m-1]
