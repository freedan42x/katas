module Each where

each :: Int -> [Int] -> [Int]
each n xs
  | null xs || n == 0 || n > length xs = []
  | n < 0 = each (-n) (reverse xs)
  | otherwise = case drop (n - 1) xs of
    x:xs -> x : each n xs
