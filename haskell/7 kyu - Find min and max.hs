module MinMax where

import Control.Monad (liftM2)

getMinMax :: [Int] -> (Int, Int)
getMinMax = liftM2 (,) minimum maximum
