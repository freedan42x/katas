module Codewars.Kata.Sheep where

countSheep :: [Bool] -> Int
countSheep = length . filter (== True)
