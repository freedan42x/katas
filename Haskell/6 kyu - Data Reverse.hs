module Codewars.Kata.DataReverse where

import Data.List.Split

dataReverse :: [Int] -> [Int]
dataReverse = concat . reverse . chunksOf 8
