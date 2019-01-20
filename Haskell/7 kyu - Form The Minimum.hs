module Min where

import Data.List

minValue :: [Int] -> Int
minValue = read . concat . (show <$>) . nub . sort
