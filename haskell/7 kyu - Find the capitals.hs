module Codewars.Kata.Capitals where

import Data.Char

capitals :: String -> [Int]
capitals s = [i | (i, c) <- zip [0..] s, isUpper c]
