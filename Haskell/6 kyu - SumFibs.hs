module Codewars.Fibonacci where

sumFibs :: Int -> Integer
sumFibs n = sum . filter even $ take (n + 1) fibs where
  fibs = 0 : 1 : zipWith (+) fibs (tail fibs)
