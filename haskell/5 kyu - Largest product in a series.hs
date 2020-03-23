module LargestProduct where

import Data.Char


productDigits :: String -> Int
productDigits = product . map digitToInt

allProducts :: String -> [Int]
allProducts str
  | length str < 5 = []
  | otherwise = productDigits (take 5 str) : allProducts (tail str)

greatestProduct :: String -> Int
greatestProduct = maximum . allProducts
