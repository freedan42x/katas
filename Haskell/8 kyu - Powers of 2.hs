module PowersOfTwo where

powersOfTwo :: Int -> [Int]
powersOfTwo n = (2 ^) <$> [0..n]
