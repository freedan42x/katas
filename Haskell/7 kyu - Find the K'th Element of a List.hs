module Kth where

import Prelude hiding ((!!))

elementAt :: [a] -> Int -> a
elementAt (x:_) 1  = x
elementAt (x:xs) e = elementAt xs (pred e)
