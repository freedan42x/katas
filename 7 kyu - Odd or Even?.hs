module Kata.OddOrEven where

oddOrEven :: Integral a => [a] -> String
oddOrEven a  = if even (sum a) then "even" else "odd"
