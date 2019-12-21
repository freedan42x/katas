module ReverseWords where

reverseWords :: String -> String
reverseWords = reverse . unwords . map reverse . words
