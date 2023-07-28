{-# LANGUAGE RankNTypes #-}
module Foldmap where

import Data.Foldable (foldMap, Foldable)
import Data.Monoid

myToList :: Foldable t => t a -> [a]
myToList = foldMap (: [])

data Min a = Min { getMin :: Maybe a }

instance Ord a => Semigroup (Min a) where
  Min Nothing <> my = my
  mx <> Min Nothing = mx
  Min (Just x) <> Min (Just y) = Min $ Just $ min x y

instance Ord a => Monoid (Min a) where
  mempty = Min Nothing

myMinimum :: (Ord a, Foldable t) => t a -> Maybe a
myMinimum = getMin . foldMap (Min . Just)

myFoldr :: Foldable t => (a -> b -> b) -> b -> t a -> b
myFoldr f z ts = appEndo (foldMap (\x -> Endo $ \y -> f x y) ts) z
