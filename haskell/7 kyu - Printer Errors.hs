module Codewars.G964.Printer where

printerError :: [Char] -> [Char]
printerError s =
  let m = length $ filter (\c -> c >= 'a' && c <= 'm') s
      n = length s - m
  in show n <> "/" <> show (m + n)
