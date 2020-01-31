module Fixit where

import Prelude hiding (reverse, foldr)


reverse' :: ([a] -> [a]) -> [a] -> [a]
reverse' _ []       = []
reverse' f (x : xs) = f xs ++ [x]

foldr' :: ((a -> b -> b) -> b -> [a] -> b) -> (a -> b -> b) -> b -> [a] -> b
foldr' _ _ b []     = b
foldr' f g b (x:xs) = g x (f g b xs)
