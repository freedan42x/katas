module Codewars.Kata.FindOdd where

findOdd :: [Int] -> Int
findOdd xs = fst . head . filter (\e -> odd $ snd e) $ func xs
  where
    func = zip xs . map (\e -> length $ filter (== e) xs)
