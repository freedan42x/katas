module SumOfJustsAndNothings where

import Data.Maybe

sumJusts :: [Maybe Integer] -> Maybe Integer
sumJusts xs = Just $ sum $ fromJust <$> filter isJust xs
