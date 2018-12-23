module Codewars.AverageCalculator where

getAverage :: [Int] -> Int
getAverage marks = div (sum marks) (length marks)
