{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, UndecidableInstances, TemplateHaskell #-}
module InvertAdd where

import InvertAddPreload

{- Imported code:
-- | The natural numbers, encoded in types.
data Z
data S n

-- | Predicate describing natural numbers.
-- | This allows us to reason with `Nat`s.
data Natural :: * -> * where
  NumZ :: Natural Z
  NumS :: Natural n -> Natural (S n)

-- | Predicate describing equality of natural numbers.
data Equal :: * -> * -> * where
  EqlZ :: Equal Z Z
  EqlS :: Equal n m -> Equal (S n) (S m)

-- | Peano definition of addition.
type family (:+:) (n :: *) (m :: *) :: *
type instance Z :+: m = m
type instance S n :+: m = S (n :+: m)
-}

reflexive :: Natural x -> Equal x x
reflexive NumZ = EqlZ
reflexive (NumS n) = EqlS $ reflexive n

trans2 :: Equal x y -> Equal x x' -> Equal y y' -> Equal x' y'
trans2 EqlZ EqlZ EqlZ = EqlZ
trans2 (EqlS a) (EqlS b) (EqlS c) = EqlS $ trans2 a b c

sucInj :: Equal (S m) (S n) -> Equal m n
sucInj (EqlS p) = p

plusSuc :: Natural a -> Natural b -> Equal (a :+: S b) (S a :+: b)
plusSuc NumZ n = reflexive $ NumS n
plusSuc (NumS m) n = EqlS $ plusSuc m n

invert :: Natural a -> Natural b -> Equal (a :+: a) (b :+: b) -> Equal a b
invert NumZ NumZ _ = EqlZ
invert (NumS m) (NumS n) p = EqlS $ invert m n $ sucInj $ trans2 (sucInj p) (plusSuc m m) (plusSuc n n)
