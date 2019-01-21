module Dutyfree where

dutyFree :: Float -> Float -> Float -> Int
dutyFree = (((floor .) . flip (/)) .) . (*) . (/ 100)
