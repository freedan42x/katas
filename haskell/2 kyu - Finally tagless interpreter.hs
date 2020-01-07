{-# LANGUAGE RankNTypes, GADTs #-}

module Tagless where

import Prelude hiding (and, or)

class Language r where
  here   :: r (a, h) a
  before :: r h a -> r (any, h) a
  lambda :: r (a, h) b -> r h (a -> b)
  apply  :: r h (a -> b) -> r h a -> r h b
  
  loop   :: r h (a -> a) -> r h a
  
  int    :: Int -> r h Int
  add    :: r h Int -> r h Int -> r h Int
  down   :: r h Int -> r h Int    -- \x -> x - 1
  up     :: r h Int -> r h Int    -- \x -> x + 1
  mult   :: r h Int -> r h Int -> r h Int
  gte    :: r h Int -> r h Int -> r h Bool -- greater than or equal
  
  bool   :: Bool -> r h Bool
  and    :: r h Bool -> r h Bool -> r h Bool
  or     :: r h Bool -> r h Bool -> r h Bool
  neg    :: r h Bool -> r h Bool
  
  ifte   :: r h Bool -> r h a -> r h a -> r h a -- if true then return left term, else return right term


data Var e a where
  VZ :: Var (a, e) a
  VS :: Var e a -> Var (x, e) a

data Expr e a where
  I    :: Int -> Expr e Int
  B    :: Bool -> Expr e Bool
  V    :: Var e a -> Expr e a
  L    :: Expr (x, e) y -> Expr e (x -> y)
  A    :: Expr e (x -> y) -> Expr e x -> Expr e y
  Add  :: Expr e Int -> Expr e Int -> Expr e Int
  Mult :: Expr e Int -> Expr e Int -> Expr e Int
  Pred :: Expr e Int -> Expr e Int
  Succ :: Expr e Int -> Expr e Int
  Gte  :: Expr e Int -> Expr e Int -> Expr e Bool
  And  :: Expr e Bool -> Expr e Bool -> Expr e Bool
  Or   :: Expr e Bool -> Expr e Bool -> Expr e Bool
  Neg  :: Expr e Bool -> Expr e Bool
  Ifte :: Expr e Bool -> Expr e a -> Expr e a -> Expr e a


instance Language Expr where
  here = V VZ
  before (V v) = V $ VS v
  lambda = L
  apply = A
  loop f = A f $ loop f
  int = I
  add = Add
  down = Pred
  up = Succ
  mult = Mult
  gte = Gte
  bool = B
  and = And
  or = Or
  neg = Neg
  ifte = Ifte


lookp :: Var e a -> e -> a
lookp VZ (x, _) = x
lookp (VS v) (_, x) = lookp v x

ap :: (a -> a -> b) -> e -> Expr e a -> Expr e a -> b
ap f e x y = parse e x `f` parse e y

parse :: e -> Expr e a -> a
parse _ (I x) = x
parse _ (B x) = x
parse e (V v) = lookp v e
parse e (L expr) = \x -> parse (x, e) expr
parse e (A f x) = parse e f $ parse e x
parse e (Add x y) = ap (+) e x y
parse e (Mult x y) = ap (*) e x y
parse e (Pred x) = pred $ parse e x
parse e (Succ x) = succ $ parse e x
parse e (Gte x y) = ap (>=) e x y
parse e (And x y) = ap (&&) e x y
parse e (Or x y) = ap (||) e x y
parse e (Neg x) = not $ parse e x
parse e (Ifte b x y) = parse e $ if parse e b then x else y


type Term a = forall r h . Language r => r h a
  
interpret :: Term a -> a
interpret = parse ()
