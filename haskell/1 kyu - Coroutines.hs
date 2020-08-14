{-# LANGUAGE LambdaCase #-}
module Coroutine where

import Control.Monad (ap, forever, when)
import Preloaded

-- Preloaded contains the following:
-- {-# LANGUAGE DeriveFunctor #-}
--
-- newtype Coroutine r u d a = Coroutine { runCoroutine :: (Command r u d a -> r) -> r } deriving (Functor)
--
-- data Command r u d a =
--   Done a
-- | Out d (Coroutine r u d a)
-- | In (u -> Coroutine r u d a) deriving Functor

-- Useful alias
apply :: Coroutine r u d a -> (Command r u d a -> r) -> r
apply = runCoroutine

instance Applicative (Coroutine r u d) where
  pure = return
  (<*>) = ap

instance Monad (Coroutine r u d) where
  return x = Coroutine $ \k -> k $ Done x
  Coroutine cr >>= g = Coroutine $ \k -> cr $ \case
    Done x  -> apply (g x) k
    Out d c -> k $ Out d $ c >>= g
    In i    -> k $ In $ \u -> i u >>= g

(>>>) :: Coroutine r u m a -> Coroutine r m d a -> Coroutine r u d a
p1 >>> p2 = Coroutine $ \k -> apply p2 $ \case
  Done x  -> k $ Done x
  Out d c -> k $ Out d $ p1 >>> c
  In i    -> apply p1 $ \case
    Done x  -> k $ Done x
    Out d c -> apply (c >>> i d) k
    In i    -> k $ In $ \u -> i u >>> p2


-- Library functions

output :: a -> Coroutine r u a ()
output v = Coroutine $ \k -> k $ Out v $ pure ()

input :: Coroutine r v d v
input = Coroutine $ \k -> k $ In pure

produce :: [a] -> Coroutine r u a ()
produce = foldr (\v r -> output v >> r) $ pure ()

consume :: Coroutine [t] u t a -> [t]
consume c = apply c $ \case
  Out d c -> d : consume c
  _       -> []

filterC p = forever $ do
  u <- input
  when (p u) $ output u

limit :: Int -> Coroutine r v v ()
limit = \case
  n | n <= 0 -> pure ()
  n -> input >>= output >> limit (n - 1)

suppress :: Int -> Coroutine r v v ()
suppress = \case
  0 -> filterC $ const True
  n -> input >> suppress (n - 1)

add :: Coroutine r Int Int ()
add = forever $ do
  m <- input
  n <- input
  output $ m + n

duplicate :: Coroutine r v v ()
duplicate = forever $ do
  u <- input
  output u
  output u

-- Programs
-- 1. A program which outputs the first 5 even numbers of a stream.
-- 2. A program which produces a stream of the triangle numbers 
-- 3. A program which multiplies a stream by 2
-- 4. A program which sums adjacent pairs of integers

p1, p2, p3, p4 :: Coroutine r Int Int ()

p1 = filterC even >>> limit 5
p2 = go 1 2 where go r k = output r >> go (r + k) (succ k)
p3 = forever $ input >>= output . (2 *)
p4 = duplicate >>> suppress 1 >>> add
