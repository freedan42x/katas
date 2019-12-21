module Kata where

findOutlier :: [Int] -> Int 
findOutlier a
  | length o > length e = e !! 0
  | otherwise = o !! 0 where
    o = filter odd a 
    e = filter even a
