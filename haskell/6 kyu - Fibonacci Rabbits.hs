module Codewars.Kata.Rabbits where


fibRabbits :: Int -> Integer -> Integer
fibRabbits n b = fs !! n where
  fs = 0 : 1 : zipWith (\x y -> b * x + y) fs (tail fs)
