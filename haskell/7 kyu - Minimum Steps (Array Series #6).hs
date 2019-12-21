module MinimumSteps where

import Data.List

minimumSteps :: [Int] -> Int -> Int
minimumSteps xs n = f 0 0 where
  a = sort xs
  f sum' i
    | sum' >= n = pred i
    | otherwise = f (sum' + a !! i) (succ i)
