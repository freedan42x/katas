module NthSmallest where

import Data.List

nthSmallest :: [Int] -> Int -> Int
nthSmallest = (. subtract 1) . (!!) . sort
