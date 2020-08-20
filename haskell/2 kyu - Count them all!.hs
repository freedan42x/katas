{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications #-}
module Counting where

import Counting.Preloaded
import Data.Proxy
import Data.Void
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Sum
import Data.Functor.Product
import Data.Functor.Compose
import Data.List
import Data.Maybe


newtype Count x = Count { getCount :: Nat } deriving (Show, Eq, Ord)


mapC :: (Nat -> Nat) -> Count a -> Count b
mapC f (Count n) = Count $ f n

liftC2 :: (Nat -> Nat -> Nat) -> Count a -> Count b -> Count c
liftC2 f (Count m) (Count n) = Count $ f m n

coerceC :: Count a -> Count b
coerceC (Count n) = Count n


class Countable c where
  count :: Count c

instance Countable Void where 
  count = Count 0

instance Countable () where
  count = Count 1

instance Countable Bool where 
  count = Count 2

inf = S inf
instance Countable Nat where 
  count = Count inf


class Factor f where
  factor :: Count c -> Count (f c)

instance (Factor f, Countable c) => Countable (f c) where
  count = (factor @f) (count @c)

instance Factor Maybe where 
  factor = mapC S

instance Factor Identity where 
  factor = coerceC

instance Factor Proxy where 
  factor = const (Count 1)

instance Factor Count where 
  factor = const (Count inf)

instance Factor [] where
  factor (Count 0) = Count 1
  factor _         = Count inf

instance Countable c => Factor (Const c) where 
  factor = const (coerceC $ count @c)

instance Countable c => Factor (Either c) where 
  factor = liftC2 (+) (count @c)

instance Countable c => Factor ((,) c) where
  factor = liftC2 (*) (count @c)

instance Countable c => Factor ((->) c) where
  factor = liftC2 (flip (^)) (count @c)

instance (Factor f, Factor g) => Factor (Sum f g) where
  factor c = liftC2 (+) (factor @f c) (factor @g c) 

instance (Factor f, Factor g) => Factor (Product f g) where
  factor c = liftC2 (*) (factor @f c) (factor @g c) 

instance (Factor f, Factor g) => Factor (Compose f g) where 
  factor = coerceC . factor @f . factor @g


class Countable a => Listable a where
  list :: [a]

instance Listable Void where 
  list = []

instance Listable () where 
  list = [()]

instance Listable Bool where 
  list = [True, False]

instance Listable Nat where 
  list = [0..]

instance Listable c => Listable (Maybe c) where 
  list = Nothing : map Just (list @c)

instance Listable c => Listable [c] where
  list = (:) [] $ [1..] >>= \n -> replicate n <$> list @c

instance (Listable a, Listable b) => Listable (Either a b) where
  list = map Left (list @a) ++ map Right (list @b)

instance (Listable a, Listable b) => Listable (a, b) where 
  list = [(a, b) | a <- list @a, b <- list @b]

instance (Eq a, Listable a, Listable b) => Listable (a -> b) where 
  list = map (\p x -> fromJust $ lookup x p) $ getByIxss r ixss
   where
    l1 = list @a
    l2 = list @b
    r = map (\x -> map (\y -> (x, y)) l2) l1
    ixss = mapM (const [0 .. length l2 - 1]) [1 .. length l1]

    getByIxss lists ixss = map (go 0) ixss
     where
      go _ []         = []
      go n (ix : ixs) = lists !! n !! ix : go (n + 1) ixs
