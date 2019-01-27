module Codewars.G964.Longest where

import Data.List

longest :: [Char] -> [Char] -> [Char]
longest = ((sort . nub) .) . (++)
