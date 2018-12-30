module Sequence.JorgeVS.Kata where

import Data.List

sequenceSum :: Int -> String
sequenceSum n
  | n < 0 = show n ++ " < 0"
  | n == 0 = "0 = 0"
  | otherwise = intercalate "+" (map show s) ++ " = " ++ a where
    s = [0..n]
    a = show $ sum s
