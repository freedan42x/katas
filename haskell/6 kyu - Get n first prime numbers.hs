module PrimeNumbers where

getPrimes :: Int -> [Int]
getPrimes n = take n [x | x <- [2..], isPrime x] where
  isPrime n = null [x | x <- [2..floor . sqrt . fromIntegral $ n], n `mod` x == 0]
