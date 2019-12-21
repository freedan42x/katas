module Zeros where

zeros :: Int -> Int
zeros 0 = 0
zeros n = (+) =<< zeros $ div n 5
