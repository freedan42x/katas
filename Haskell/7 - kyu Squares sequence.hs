module Codewars.Exercise.Squares where

squares :: Integer -> Int -> [Integer]
squares x n = take n $ iterate (^2) x
