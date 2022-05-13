{-# LANGUAGE LambdaCase #-}
module BinarySearchTrees () where

import Preloaded (Tree(Tree))


instance Show Tree where
  show = showTreeElem . Just
   where
    showTreeElem = maybe "_" $ \case
      Tree node Nothing Nothing -> "[" <> show node <> "]"
      Tree node l r ->
        concat ["[", showTreeElem l, " ", show node, " ", showTreeElem r, "]"]

instance Eq Tree where
  Tree n l r == Tree n' l' r' = n == n' && l == l' && r == r'
