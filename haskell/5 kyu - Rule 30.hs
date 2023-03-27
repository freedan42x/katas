module Codewars.Kata.Rule30 (rule30) where

import Data.Bits


rule30 :: [Int] -> Int -> [Int]
rule30 cells n = iterate step cells !! n
 where
   step xs = zipWith3 (\x y z -> xor x $ y .|. z)
               ([0, 0] <> xs)
               ([0] <> xs <> [0])
               (xs <> [0, 0])
