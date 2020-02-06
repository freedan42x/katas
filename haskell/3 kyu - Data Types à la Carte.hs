{-# LANGUAGE TypeOperators, DeriveFunctor, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, OverlappingInstances #-}
module ALaCarte where


data Expr f = In (f (Expr f))

data Lit a = Lit Int
data Add a = Add a a

data (f :+: g) e = Inl (f e) | Inr (g e)
infixr 1 :+:


instance Functor Lit where
  fmap _ (Lit n) = Lit n

instance Functor Add where
  fmap f (Add m n) = Add (f m) (f n)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl a) = Inl $ f <$> a
  fmap f (Inr b) = Inr $ f <$> b

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In e) = f $ foldExpr f <$> e


class Functor f => Eval f where
  evalAlgebra :: f Int -> Int

instance Eval Lit where
  evalAlgebra (Lit x) = x

instance Eval Add where
  evalAlgebra (Add x y) = x + y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra (Inl l) = evalAlgebra l
  evalAlgebra (Inr r) = evalAlgebra r
  
eval :: Eval f => Expr f -> Int
eval = foldExpr evalAlgebra


class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a

instance Functor f => f :<: f where
  inj = id

instance (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl

instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj


inject :: (g :<: f) => g (Expr f) -> Expr f
inject = In . inj

lit :: (Lit :<: f) => Int -> Expr f
lit = inject . Lit

add :: (Add :<: f) => Expr f -> Expr f -> Expr f
add = (inject .) . Add


data Mult a = Mult a a deriving Functor

instance Eval Mult where
  evalAlgebra (Mult m n) = m * n

mult :: (Mult :<: f) => Expr f -> Expr f -> Expr f
mult = (inject .) . Mult


class Functor f => Pretty f where
  prettyAlgebra :: f String -> String

pretty :: Pretty f => Expr f -> String
pretty = foldExpr prettyAlgebra

instance Pretty Lit where
  prettyAlgebra (Lit n) = show n

instance Pretty Add where
  prettyAlgebra (Add m n) = concat ["(", m, "+", n, ")"]

instance Pretty Mult where
  prettyAlgebra (Mult m n) = concat ["(", m, "*", n, ")"]

instance (Pretty f, Pretty g) => Pretty (f :+: g) where
  prettyAlgebra (Inl l) = prettyAlgebra l
  prettyAlgebra (Inr r) = prettyAlgebra r
