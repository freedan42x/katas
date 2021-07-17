module Fibonacci where

fib :: Int -> Integer
fib = (fibs !!) . pred where
  fibs = 0 : 1 : zipWith (+) fibs (tail fibs)
