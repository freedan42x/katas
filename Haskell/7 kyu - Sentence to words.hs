module SentenceToWords where

import Data.List.Split

splitSentence :: [Char] -> [[Char]]
splitSentence = splitOn " "
