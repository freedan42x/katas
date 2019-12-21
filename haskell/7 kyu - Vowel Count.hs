module Codewars.Kata.Vowel where

getCount :: String -> Int
getCount = length . filter (`elem` "aeiou")
