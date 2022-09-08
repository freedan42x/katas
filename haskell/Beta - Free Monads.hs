{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
module FreeMonads where

import Data.Functor
import Data.Functor.Sum
import Control.Monad
import Preloaded

{-
preloaded:

data Free f a
  = Pure a
  | Free (f (Free f a))
-}

-- Just by requiring that f is a Functor, we can implement Functor,
-- Applicative, and Monad instances
-- for Free f a
instance Functor f => Functor (Free f) where
  fmap = liftM

instance Functor f => Applicative (Free f) where
  pure  = return
  (<*>) = ap

instance Functor f => Monad (Free f) where
  return = Pure
  Pure x >>= f = f x
  Free r >>= f = Free $ fmap (>>= f) r

-- we can use Free to implement mtl's Reader, Writer, and State
-- To create an effect type, we create constructors for each "core" operation

-- The Reader effect helps automate parameter passing
-- It allows you to `Ask` for or "read" the `r` parameter
data Reader r a = Ask (r -> a) deriving Functor

-- we must lift the Ask into the Free type so we can use it in do-notation
ask :: Free (Reader r) r
ask = Free $ Ask pure

-- we can even implement local without knowing anything about how to evaluate
-- `Free (Reader r) a`! local's job is to apply the given function to
-- the result of any `Ask` in the provided computation This is not mutation,
-- since the change only occurs in the specified computation
local :: (r -> r) -> Free (Reader r) a -> Free (Reader r) a
local f k = liftFree $ Ask $ \x -> runReader (f x) k

-- This is where we define the semantics of Reader. 
-- The desired semantics are that all `Ask`s are supplied with the given `r`
runReader :: r -> Free (Reader r) a -> a
runReader _ (Pure k      ) = k
runReader x (Free (Ask r)) = runReader x $ r x

-- multiply the reader value by 2
double :: Free (Reader Int) Int
double = local (* 2) ask

-- from preloaded:
-- data BT = Leaf Int | Node BT BT

-- Replace each node's value with its depth in the tree
-- The reader value is the current depth
labelDepth :: BT -> Free (Reader Int) BT
labelDepth (Leaf _) = do
  d <- ask
  pure $ Leaf d
labelDepth (Node l r) = do
  l' <- local succ $ labelDepth l
  r' <- local succ $ labelDepth r
  pure $ Node l' r'

-- We can generalize the process of lifting effect constructors to the
-- `Free f a` to make it easier to implement functions like `ask`
liftFree :: Functor f => f a -> Free f a
liftFree x = Free $ fmap pure x

-- The Writer effect is useful for logging.
-- We can log a `w` value by `Tell`ing it
data Writer w a = Tell w a deriving Functor

-- HINT: use liftFree
tell :: w -> Free (Writer w) ()
tell w = liftFree $ Tell w ()

-- The desired semantics of the Writer effect is that every value `Tell`ed
-- gets accumulated in a monoid in chronological order
runWriterMonoid :: Monoid w => Free (Writer w) a -> (w, a)
runWriterMonoid (Pure x) = (mempty, x)
runWriterMonoid (Free (Tell w r)) =
  let (w', x) = runWriterMonoid r in (w <> w', x)

-- We can interpret an effect in many ways.
-- For example, we can elide the monoid restriction on `w`
-- and instead accumulate all tells in a list
runWriterList :: Free (Writer w) a -> ([w], a)
runWriterList (Pure x         ) = ([], x)
runWriterList (Free (Tell w r)) = let (ws, x) = runWriterList r in (w : ws, x)

-- flatten a binary tree to a list
-- (we'll use the list interpreter)
flatten :: BT -> Free (Writer Int) ()
flatten (Leaf x  ) = tell x
flatten (Node l r) = flatten l >> flatten r

-- compute the sum of elements in a list, and also log every element as a string
showAndSum :: [Int] -> Free (Writer String) Int
showAndSum []       = pure 0
showAndSum (x : xs) = tell (show x) >> fmap (x +) (showAndSum xs)

-- The State effect can emulate mutable state.
-- `Get` retrieves the state and `Put` sets it.
-- In general, operations which input or request information use a function type,
-- and operations which output information use a product type
-- Think about how nesting these functors inside of themselves
-- represents a multi-step computation
data State s a
  = Get (s -> a)
  | Put s a
  deriving Functor

get :: Free (State s) s
get = liftFree $ Get id

put :: s -> Free (State s) ()
put s = liftFree $ Put s ()

-- modify applies a function to the state and sets it to the result
modify :: (s -> s) -> Free (State s) ()
modify f = do
  x <- get
  put $ f x

-- `Get`s should be supplied with current state,
-- and `Put` should set the state
-- such that subsequent `Get` calls are supplied the new state
-- We take in the initial state
-- The final state should be returned along side the result
runState :: s -> Free (State s) a -> (s, a)
runState s (Pure x         ) = (s, x)
runState s (Free (Get f   )) = runState s $ f s
runState _ (Free (Put s' x)) = runState s' x

-- add each value to the state
sumList :: [Int] -> Free (State Int) ()
sumList = put . sum

-- compute the nth fibonacci number where the initial state is (fib(0), fib(1))
-- HINT: think of a while loop. don't do fib (n - 1) + fib (n - 2)
fibState :: Int -> Free (State (Int, Int)) Int
fibState n = do
  replicateM_ n $ do
    (a, b) <- get
    put (b, a + b)

  fst <$> get

-- If supplied a natural transformation between functors, we can change the functor of a `Free`
hoist :: Functor f => (forall x . f x -> g x) -> Free f a -> Free g a
hoist _ (Pure x) = Pure x
hoist f (Free r) = Free $ f $ fmap (hoist f) r

-- `Sum` is like `Either` for functors. It is defined as follows:
-- data Sum f g a = InL (f a) | InR (g a)

-- The sum of two functors is also a functor.
-- This can be used to compose effects! 
-- If we sum two effects, we can use them at the same time using these helpers:

-- We can use this function to lift an effect into a sum where it is on the left
inL :: Functor f => Free f a -> Free (Sum f g) a
inL = hoist InL

-- We can use this function to lift an effect into a sum where it is on the right
inR :: Functor g => Free g a -> Free (Sum f g) a
inR = hoist InR

-- You don't have to interpret the whole sum at once
-- You can just define how to interpret a specific functor out of the sum
-- and chain these eliminations to interpret the whole sum

-- define how to interpret reader effects out of a sum
elimReader :: Functor f => r -> Free (Sum (Reader r) f) a -> Free f a
elimReader _ (Pure x            ) = Pure x
elimReader r (Free (InL (Ask f))) = elimReader r $ f r
elimReader r (Free (InR k      )) = Free $ elimReader r <$> k

-- define how to intepret writer effects out of a sum
-- (use the monoid interpretation)
elimWriter
  :: (Functor f, Monoid w) => Free (Sum (Writer w) f) a -> Free f (w, a)
elimWriter (Pure x) = Pure (mempty, x)
elimWriter (Free (InL (Tell w r))) =
  (\(w', x) -> (w <> w', x)) <$> elimWriter r

-- now, without interpreting the whole sum directly,
-- write an interpreter for reader and writer
-- you shouldn't need to pattern match
runReaderWriter :: Monoid w => r -> Free (Sum (Reader r) (Writer w)) a -> (w, a)
runReaderWriter r k = runWriterMonoid $ elimReader r k

-- using reader and writer at the same time,
-- write a function that reads a value and then tells it
passItOn :: Free (Sum (Reader a) (Writer a)) ()
passItOn = inL ask >>= inR . tell
