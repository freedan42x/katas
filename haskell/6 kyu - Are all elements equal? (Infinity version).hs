module EqAll.Kata (eqAll) where

import Data.Foldable (toList)


eqAll :: (Foldable t, Eq a) => t a -> Bool
eqAll xs = case toList xs of
  []     -> True
  x : xs -> all (x ==) xs
