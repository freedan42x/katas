module IsPrime where

isPrime :: Integer -> Bool
isPrime 0 = False
isPrime 1 = False
isPrime x = [1] == divisors x where
  divisors n = 1 : concat [[m, n `div` m] | m <- [2..floor . sqrt . fromIntegral $ n], n `rem` m == 0]
