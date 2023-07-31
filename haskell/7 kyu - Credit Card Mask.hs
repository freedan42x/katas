module Maskify where

maskify :: String -> String
maskify xs = [if i + 4 < length xs then '#' else x | (i, x) <- zip [0..] xs]
