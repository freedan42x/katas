module Mixed where

import Control.Monad
import Data.Either

sumMix :: [Either String Int] -> Int
sumMix = sum . ap ((++) . map read . lefts) rights
