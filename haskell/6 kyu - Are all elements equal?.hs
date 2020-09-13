module EqAll.Kata (eqAll) where

import Data.List (nub)


eqAll :: Eq a => [a] -> Bool
eqAll = (2 >) . length . nub
