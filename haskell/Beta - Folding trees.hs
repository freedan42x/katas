module Folds where


data LeafTree a 
  = LeafNode (LeafTree a) (LeafTree a) 
  | LeafLeaf a
  deriving (Show, Eq)
    
data BiTree a 
  = BiNode a (BiTree a) (BiTree a) 
  | BiLeaf
  deriving (Show, Eq)
  
data RoseTree a 
  = RoseNode a [RoseTree a]
  deriving (Show, Eq)

foldLeafTree :: (b -> b -> b) -> (a -> b) -> LeafTree a -> b
foldLeafTree _ g (LeafLeaf a) = g a
foldLeafTree f g (LeafNode l r) = f (foldLeafTree f g l) (foldLeafTree f g r)

foldBiTree :: (a -> b -> b -> b) -> b -> BiTree a -> b
foldBiTree _ b BiLeaf = b
foldBiTree f b (BiNode a l r) = f a (foldBiTree f b l) (foldBiTree f b r)

foldRoseTree :: (a -> b -> c) -> (c -> b -> b) -> b -> RoseTree a -> c
foldRoseTree f g b (RoseNode x rs) = f x $ foldr (g . foldRoseTree f g b) b rs
