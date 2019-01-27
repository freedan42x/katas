module ISBN10 where

import Data.Char

validISBN10 :: String -> Bool
validISBN10 str
  | 'X' `elem` str && last str /= 'X' = False
  | length (filter (\e -> not $ e `elem` "123456789X") str) > 0 = False
  | length str == 10 = sum (zipWith (*) (func str) [1..10]) `mod` 11 == 0
  | otherwise = False
    where
      func str
        | last str == 'X' = map digitToInt (reverse . drop 1 $ reverse str) ++ [10]
        | otherwise = map digitToInt str
