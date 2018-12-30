module NumbersInOrder (isAscOrder) where 

import Data.List (sort)

isAscOrder :: [Int] -> Bool
isAscOrder a = a == sort a
