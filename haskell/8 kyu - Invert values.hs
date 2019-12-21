module Kata (invert) where

invert :: [Integer] -> [Integer]
invert arr = map (*(-1)) arr
