module Kata (remove) where

remove :: String -> Int -> String
remove str x = f str x 0 "" where
  f s c i ns
    | length s == i = ns
    | otherwise = f s (if s !! i == '!' then c - 1 else c) (i + 1) (if s !! i == '!' && c > 0 then ns ++ "" else ns ++ [s !! i])
