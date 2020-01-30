{-# LANGUAGE 
  FlexibleInstances, 
  UndecidableInstances, 
  InstanceSigs,
  ScopedTypeVariables,
  RankNTypes #-}

module PC where

import Data.List

type ISO a b = (a -> b, b -> a)

symm :: ISO a b -> ISO b a
symm (ab, ba) = (ba, ab)

substL :: ISO a b -> (a -> b)
substL = fst

substR :: ISO a b -> (b -> a)
substR = snd

liftISO2 :: ISO a b -> ISO (a -> a -> a) (b -> b -> b)
liftISO2 (ab, ba) = 
  (\f x y -> ab $ f (ba x) (ba y)
  ,\f x y -> ba $ f (ab x) (ab y))


class Nat n where
  zero :: n
  successor :: n -> n
  nat :: a -> (n -> a) -> n -> a
  iter :: a -> (a -> a) -> n -> a
  plus, minus, mult, pow :: n -> n -> n
  inf :: n
  inf = successor inf
  divide :: n -> n -> n
  l `divide` r | l == 0 && r == 0 = undefined
  l `divide` r | l < r = 0
  l `divide` r | otherwise = successor $ (l `minus` r) `divide` r
  isoP :: ISO n Peano
  isoP = (iter zero successor, iter zero successor)
  toP :: n -> Peano
  toP = substL isoP

instance {-# OVERLAPPABLE #-} Nat n => Show n where
  show = show . toP

instance {-# OVERLAPPABLE #-} Nat n => Eq n where
  l == r = toP l == toP r

instance {-# OVERLAPPABLE #-} Nat n => Ord n where
  l `compare` r = toP l `compare` toP r

instance {-# OVERLAPPABLE #-} Nat n => Num n where
  abs = id
  signum = nat zero (const 1)
  fromInteger 0 = zero
  fromInteger n | n > 0 = successor $ fromInteger (n - 1)
  (+) = plus
  (*) = mult
  (-) = minus

data Peano = O | S Peano deriving (Show, Eq, Ord)
instance Nat Peano where
  zero            = O
  successor       = S
  nat z _       O = z
  nat _ s   (S p) = s p
  iter a _      O = a
  iter a f  (S p) = f (iter a f p)
  O   `plus`    n = n
  S m `plus`    n = S (m `plus` n)
  O   `mult`    _ = O
  S m `mult`    n = n `plus` (m `mult` n)
  _   `pow`     O = S O
  m   `pow`   S n = m `mult` (m `pow` n)
  O   `minus`   _ = O
  m   `minus`   O = m
  S m `minus` S n = m `minus` n

instance Nat [()] where
  zero = []
  successor = (():)
  nat z _ [] = z
  nat _ s (_:l) = s l
  iter a _ [] = a
  iter a f (_:l) = f (iter a f l)
  plus       = (++)
  mult l l'  = replicate (length l * length l') ()
  pow l l'   = replicate (length l ^ length l') ()
  minus l l' = drop (length l') l

newtype Scott = Scott { runScott :: forall a. a -> (Scott -> a) -> a }
instance Nat Scott where
  zero = Scott const
  successor n = Scott (\_ s -> s n)
  nat a f (Scott sc) = sc a f
  iter a f (Scott sc) = sc a (\s -> f (iter a f s))
  plus = substR (liftISO2 isoP) plus
  minus = substR (liftISO2 isoP) minus
  mult = substR (liftISO2 isoP) mult
  pow = substR (liftISO2 isoP) pow

fromChurch (Church c) = c S O
newtype Church = Church { runChurch :: forall a. (a -> a) -> a -> a }
instance Nat Church where
  zero = Church (\_ z -> z)
  successor (Church c) = Church (\s z -> s (c s z))
  nat a f c = nat a (f . toChurch) (fromChurch c)
    where
      toChurch O = zero
      toChurch (S n) = successor (toChurch n)
  iter a f c = iter a f (fromChurch c)
  Church m `plus` Church n = Church (\s z -> m s (n s z))
  Church m `mult` Church n = Church (\s z -> m (n s) z)
  m `pow`   n = substR isoP (toP m `pow` toP n)
  m `minus` n = substR isoP (toP m `minus` toP n)
