module Stream where

import Control.Arrow
import Control.Applicative

import Stream.Internal

-- Defined in Stream.Internal:
--     data Stream a = a :> Stream a
--     infixr :>

-- | Get the first element of a stream.
headS :: Stream a -> a
headS (a :> _) = a

-- | Drop the first element of a stream.
tailS :: Stream a -> Stream a
tailS (_ :> s) = s


-- {{{ Stream constructors

-- | Construct a stream by repeating a value.
repeatS :: a -> Stream a
repeatS a = a :> repeatS a

-- | Construct a stream by repeatedly applying a function.
iterateS :: (a -> a) -> a -> Stream a
iterateS f a = a :> iterateS f (f a)

-- | Construct a stream by repeating a list forever.
cycleS :: [a] -> Stream a
cycleS xs = f xs
  where
    f []     = f xs
    f (y:ys) = y :> f ys

-- | Construct a stream by counting numbers starting from a given one.
fromS :: Num a => a -> Stream a
fromS a = a :> fromS (a + 1)

-- | Same as 'fromS', but count with a given step width.
fromStepS :: Num a => a -> a -> Stream a
fromStepS x s = x :> fromStepS (x + s) s

-- }}}


-- | Fold a stream from the left.
foldrS :: (a -> b -> b) -> Stream a -> b
foldrS f (x :> xs) = f x (foldrS f xs)

-- | Filter a stream with a predicate.
filterS :: (a -> Bool) -> Stream a -> Stream a
filterS p (x :> xs)
  | p x       = x :> filterS p xs
  | otherwise = filterS p xs

-- | Take a given amount of elements from a stream.
takeS :: Int -> Stream a -> [a]
takeS n (x :> xs)
  | n <= 0    = []
  | otherwise = x : takeS (n - 1) xs

-- | Drop a given amount of elements from a stream.
dropS :: Int -> Stream a -> Stream a
dropS n s@(x :> xs) 
  | n <= 0    = s
  | otherwise = dropS (n - 1) xs

-- | Do take and drop simultaneous.
splitAtS :: Int -> Stream a -> ([a], Stream a)
splitAtS i s = (takeS i s, dropS i s)

-- | Combine two streams with a function.
zipWithS :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithS f (x :> xs) (y :> ys) = f x y :> zipWithS f xs ys

zipS :: Stream a -> Stream b -> Stream (a, b)
zipS = zipWithS (,)

instance Functor Stream where
    -- fmap :: (a -> b) -> Stream a -> Stream b
    fmap f (x :> xs) = f x :> fmap f xs

instance Applicative Stream where
    -- pure :: a -> Stream a
    pure = repeatS

    -- (<*>) :: Stream (a -> b) -> Stream a -> Stream b
    f :> fs <*> x :> xs = f x :> (fs <*> xs)

-- | The stream of fibonacci numbers.
fibS :: Stream Integer
fibS = cycleS fibs
  where
    fibs = 0 : 1 : zipWith (+) fibs (tail fibs)

-- | The stream of prime numbers.
primeS :: Stream Integer
primeS = cycleS primes
  where
    filterPrime (p:xs) = p : filterPrime [x | x <- xs, x `mod` p /= 0]
    primes = filterPrime [2..]
