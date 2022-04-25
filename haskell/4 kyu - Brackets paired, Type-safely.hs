{-# LANGUAGE KindSignatures, DataKinds, GADTs, PolyKinds, ScopedTypeVariables, TypeApplications #-}

module Kata.PairedBracket where 


data Nat = Z | S Nat deriving Show

instance Show (Paren n) where
    show PEmpty = ""
    show (PLeft p) = '(' : show p
    show (PRight p) = ')' : show p

instance Eq (Paren n) where
    PEmpty == PEmpty = True
    (PLeft n1) == (PLeft n2)  = n1 == n2
    (PRight n1) == (PRight n2)  = n1 == n2
    _ == _ = False

data Paren :: Nat -> * where
    PEmpty ::Paren Z
    PLeft ::Paren (S n) -> Paren n
    PRight ::Paren n -> Paren (S n)

data SNat :: Nat -> * where
  Zero ::SNat Z
  Suc ::SNat n -> SNat (S n)

class Sing n where
  sing :: SNat n

instance Sing Z where
  sing = Zero

instance Sing n => Sing (S n) where
  sing = Suc sing

data Proxy (a :: k) where
  Proxy ::Proxy a

data SomeNat where
  SomeNat ::Sing n => Proxy n -> SomeNat

toNat :: Int -> SomeNat
toNat 0 = SomeNat (Proxy :: Proxy Z)
toNat n = case toNat (n - 1) of
  SomeNat (p :: Proxy n) -> SomeNat (Proxy :: Proxy (S n))

putLeft :: SNat n -> Paren n -> Paren Z
putLeft Zero    k = k
putLeft (Suc n) k = putLeft n (PLeft k)

putRight :: SNat n -> Paren n
putRight Zero    = PEmpty
putRight (Suc n) = PRight $ putRight n

makeNestedParenOfSize :: Int -> Paren Z
makeNestedParenOfSize x
  | x <= 0 = PEmpty
  | otherwise = case toNat x of
    SomeNat (p :: Proxy n) -> let k = sing @n in putLeft k $ putRight k
