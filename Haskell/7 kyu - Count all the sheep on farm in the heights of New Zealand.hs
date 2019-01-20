module Sheep where

lostSheep :: [Int] -> [Int] -> Int -> Int
lostSheep = (. sum) . flip . ((-) .) . subtract . sum
