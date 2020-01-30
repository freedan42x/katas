module Flatten where

data Tree a = Leaf | Branch (Tree a) a (Tree a) deriving (Show, Eq)

single :: a -> Tree a
single a = Branch Leaf a Leaf

invert :: Tree a -> Tree a
invert Leaf = Leaf
invert (Branch l n r) = Branch (invert r) n (invert l)

size :: Tree a -> Int
size Leaf = 0
size (Branch l n r) = size l + 1 + size r

flatten :: Tree a -> [a]
flatten Leaf = []
flatten (Branch l n r) = flatten l ++ [n] ++ flatten r
