module TreeTop where

data Tree a = Nil | Node (Tree a) a (Tree a) deriving (Show)

treeTop :: Tree Int -> [Int]
treeTop Nil = []
treeTop (Node l x r) = left l <> [x] <> right r
  where
    left Nil = []
    left (Node l x _) = left l <> [x]

    right Nil = []
    right (Node _ x r) = x : right r
