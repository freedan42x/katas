module Factorial where

factorial :: Integer -> Integer
factorial = product . enumFromTo 1
