module Codewars.Oddities where

noOdds :: Integral n => [n] -> [n]
noOdds = filter even
