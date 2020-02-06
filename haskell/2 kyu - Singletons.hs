{-# LANGUAGE GADTs, DataKinds, TypeFamilies, TypeOperators #-}
module Singletons where

import Prelude hiding (drop, take, head, tail, index, zipWith, replicate, map, (++))


data Vec a n where
  VNil  :: Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)

data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat

data SNat a where
  SZero :: SNat Zero
  SSucc :: SNat a -> SNat (Succ a)


type family (a :: Nat) :< (b :: Nat) :: Bool where
  m      :< Zero   = False
  Zero   :< Succ n = True
  Succ m :< Succ n = m :< n

type family (a :: Nat) :+ (b :: Nat) :: Nat where
  Zero   :+ n = n
  Succ m :+ n = Succ (m :+ n)

type family Min (a :: Nat) (b :: Nat) :: Nat where
  Min Zero     n        = Zero
  Min m        Zero     = Zero
  Min (Succ m) (Succ n) = Succ (Min m n)

type family (a :: Nat) :- (b :: Nat) :: Nat where
  Zero   :- n      = Zero
  m      :- Zero   = m
  Succ m :- Succ n = m :- n


map :: (a -> b) -> Vec a n -> Vec b n
map f VNil         = VNil
map f (VCons x xs) = VCons (f x) (map f xs)

index :: (a :< b) ~ True => SNat a -> Vec s b -> s
index SZero     (VCons x _)  = x
index (SSucc n) (VCons _ xs) = index n xs

replicate :: s -> SNat a -> Vec s a
replicate _ SZero     = VNil
replicate s (SSucc n) = VCons s (replicate s n)

zipWith :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWith _ VNil         VNil         = VNil
zipWith f (VCons x xs) (VCons y ys) = VCons (f x y) (zipWith f xs ys) 

(++) :: Vec v m -> Vec v n -> Vec v (m :+ n)
VNil       ++ ys = ys 
VCons x xs ++ ys = VCons x (xs ++ ys)

take :: SNat a -> Vec v n -> Vec v (Min a n)
take SZero     _            = VNil
take _         VNil         = VNil
take (SSucc n) (VCons x xs) = VCons x (take n xs)

drop :: SNat a -> Vec v n -> Vec v (n :- a)
drop SZero     xs           = xs
drop _         VNil         = VNil
drop (SSucc n) (VCons _ xs) = drop n xs 

head :: (Zero :< n) ~ True => Vec v n -> v
head (VCons x _) = x

tail :: Vec v n -> Vec v (n :- Succ Zero)
tail (VCons _ xs) = xs
