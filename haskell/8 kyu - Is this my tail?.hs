module Codewars.IsThisMyTail where

correctTail :: String -> Char -> Bool
correctTail = (==) . last
