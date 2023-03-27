module Sieve where

primes :: Int -> [Int]
primes k = takeWhile (<= k) $ helper [2..]
 where
   helper (x:xs) = x : helper (filter (\y -> y `mod` x /= 0) xs)
