module MaxSize where
import Data.List

maxProduct :: [Integer] -> Int -> Integer
maxProduct = flip ((product .) . take) . reverse . sort
