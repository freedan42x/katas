module Fibonacci where

import Data.List
import Data.Bits
 
fibonacci :: Int -> Integer
fibonacci n = snd . foldl_ fib_ (1, 0) . dropWhile not $
            [testBit n k | k <- let s = bitSize n in [s - 1,s - 2..0]]
    where
        fib_ (f, g) p
            | p         = (f * (f + 2 * g), ss)
            | otherwise = (ss, g * (2 * f - g))
            where ss = f * f + g * g
        foldl_ = foldl' -- '
