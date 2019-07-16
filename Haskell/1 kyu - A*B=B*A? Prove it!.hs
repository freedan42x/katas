{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, UndecidableInstances #-}

module Kata.TimesComm where

import Kata.TimesComm.Definitions


plus :: Natural a -> Natural b -> Natural (a :+: b)
plus NumZ b     = b
plus (NumS a) b = NumS $ plus a b

mult :: Natural a -> Natural b -> Natural (a :*: b)
mult NumZ _     = NumZ
mult (NumS a) b = plus b (mult a b)

eq :: Natural a -> Natural b -> Equal a b
eq NumZ NumZ         = EqlZ
eq (NumS a) (NumS b) = EqlS $ eq a b

timesComm :: Natural a -> Natural b -> Equal (a :*: b) (b :*: a)
timesComm a b = eq (mult a b) (mult b a)
-- Ok....
