module GuessTheArray where

guess :: Integral n => (Int -> Int -> n) -> Int -> [n]
guess f len = helper 0 where
  helper k
    | len == k = []
    | len - k >= 3 = let x = (f k (k + 1) + f k (k + 2) - f (k + 1) (k + 2)) `div` 2
                         y = f k (k + 1) - x
                         z = f (k + 1) (k + 2) - y
                     in x : y : z : helper (k + 3)
    | otherwise = drop (3 - len + k) $ helper (len - 3)
