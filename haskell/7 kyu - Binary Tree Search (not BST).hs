module BinaryTreeSearch where


data Tree a = Nil | Node (Tree a) a (Tree a) deriving Show

search :: Int -> Tree Int -> Bool
search _ Nil = False
search n (Node a v b) = n == v || search n a || search n b
