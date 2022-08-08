module NIM where

import Data.Bits
import Data.List


-- | Returns the index and the number picked from a board
chooseMove :: [Int] -> (Int, Int)
chooseMove piles =
 let
  s = foldl xor 0 piles
  hs = map (xor s) piles
 in
  case findIndex (uncurry (<)) $ zip hs piles of
    Just i -> (i, piles !! i - hs !! i)
    _ -> error "Loss"
