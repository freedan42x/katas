module Codewars.G964.Thirteen where

import Data.Char


thirt :: Integer -> Integer
thirt n | n == r    = n
        | otherwise = thirt r
 where
  r = toInteger $ sum $ zipWith (*) (reverse $ digitToInt <$> show n) $ cycle
    [1, 10, 9, 12, 3, 4]
