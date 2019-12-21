module Codewars.G964.Sumdivsq where

listSquared :: Int -> Int -> [(Int, Int)]
listSquared m n = [(i, func i) | i <- [m..n], func i /= 0] where
  func n = if ceiling s == floor s then (floor s) ^ 2 else 0 where
    s = sqrt . fromIntegral . sum $ map (^ 2) (divisors n ++ [n `div` i | i <- divisors n, i * i /= n])
  divisors n = [i | i <- [1..floor . sqrt . fromIntegral $ n], n `rem` i == 0]
