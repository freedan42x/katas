module Codewars.Kata.Spinning where

spinWords :: String -> String
spinWords = unwords . map (\x -> if length x > 4 then reverse x else x) . words
