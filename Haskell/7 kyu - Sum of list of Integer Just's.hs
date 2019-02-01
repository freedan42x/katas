module SumOfJusts where

import Data.Maybe

sumJusts :: [Maybe Integer] -> Maybe Integer
sumJusts = Just . sum . catMaybes
