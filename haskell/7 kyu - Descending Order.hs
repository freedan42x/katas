module DescendingOrder where

import Data.Char
import Data.List

descendingOrder :: Integer -> Integer
descendingOrder = read . concatMap show . reverse . sort . map digitToInt . show
