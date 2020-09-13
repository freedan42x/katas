module KthElement where

import Prelude hiding ((!!))


-- | Returns Just the k-th element of the list, or Nothing if k is out of bounds.
elementAt :: Int -> [a] -> Maybe a
elementAt _ []      = Nothing
elementAt 1 (x : _) = Just x
elementAt n (_ : xs) | n < 1     = Nothing
                     | otherwise = elementAt (pred n) xs
