module TaylorSeries (exp, sin, cos, eval) where

import Prelude hiding (exp, sin, cos)
import Data.Ratio

type TaylorSeries = [Rational]

fac 0 = 1
fac n = n * fac (n - 1)

exp :: TaylorSeries
exp = [1 % fac x | x <- [0..]]

sin :: TaylorSeries
sin = 0 : map f [0..] where
  f n | odd n = 0
      | odd (n `div` 2) = (-1) % fac (n + 1)
      | otherwise = 1 % fac (n + 1)

cos :: TaylorSeries
cos = 1 : map f [0..] where
  f n | even n = 0
      | even (n `div` 2) = (-1) % fac (n + 1)
      | otherwise = 1 % fac (n + 1)

eval :: TaylorSeries -> Double -> Int -> Double
eval ps x n = sum $ map (\(i, k) -> fromRational k * x ^ i) $ zip [0..] $ take n ps
