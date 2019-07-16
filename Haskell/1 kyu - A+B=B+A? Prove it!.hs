{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module Kata.AdditionCommutes where

import Kata.AdditionCommutes.Definitions


plus :: Natural a -> Natural b -> Natural (a :+: b)
plus NumZ b = b
plus (NumS a) b = NumS $ plus a b

eq :: Natural a -> Natural b -> Equal a b
eq NumZ NumZ = EqlZ
eq (NumS a) (NumS b) = EqlS $ eq a b

-- Well... I spent many hours trying to prove this and came up with this retarded solution.
plusCommutes :: Natural a -> Natural b -> Equal (a :+: b) (b :+: a)
plusCommutes a b = eq (plus a b) (plus b a)
