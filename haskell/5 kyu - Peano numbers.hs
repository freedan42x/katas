module Haskell.Codewars.Peano where

import Prelude hiding (even, odd, div, compare, Num, Int, Integer, Float, Double, Rational, Word)


data Peano = Zero | Succ Peano deriving (Eq, Show)


add, sub, mul, div :: Peano -> Peano -> Peano

Zero   `add` n = n
Succ m `add` n = Succ $ m `add` n

Zero   `sub` Succ _ = error "negative number"
m      `sub` Zero   = m
Succ m `sub` Succ n = m `sub` n

Zero   `mul` _ = Zero
Succ m `mul` n = n `add` (m `mul` n)

_ `div` Zero = error "divide by 0"
Zero `div` _ = Zero
m    `div` n = 
  case compare m n of
    LT -> Zero
    _  -> Succ $ (m `sub` n) `div` n


even, odd :: Peano -> Bool

even Zero = True
even (Succ n) = odd n

odd Zero = False
odd (Succ n) = even n


compare :: Peano -> Peano -> Ordering
Zero   `compare` Zero   = EQ
Zero   `compare` Succ _ = LT
Succ _ `compare` Zero   = GT
Succ m `compare` Succ n = m `compare` n
