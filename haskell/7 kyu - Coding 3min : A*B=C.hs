module FindAB where

findAB :: [Int] -> Int -> Maybe (Int,Int)
findAB [] _ = Nothing
findAB xs 0 = Just (head xs, 0)
findAB (x:xs) n
  | x == 0                        = findAB xs n
  | f `elem` xs && n `rem` x == 0 = Just (n `div` f, f)
  | otherwise                     = findAB xs n where
    f                             = n `div` x
