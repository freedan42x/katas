module Pillars where

pillars :: Int -> Int -> Int -> Int
pillars cnt dist width = max 0 $ dist * 100 * (cnt - 1) + width * (cnt - 2)
