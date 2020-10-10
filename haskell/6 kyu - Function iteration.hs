module IterateN (iterateN) where

iterateN :: Int -> (a -> a) -> (a -> a)
iterateN 0 f x = x
iterateN n f x = f $ iterateN (n - 1) f x
