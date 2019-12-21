module Haskell.Codewars.Church where

type Lambda a = (a -> a)
type Cnum a = Lambda a -> Lambda a

churchAdd :: Cnum a -> Cnum a -> Cnum a
churchAdd m n = (\f x -> n f (m f x))

churchMul :: Cnum a -> Cnum a -> Cnum a
churchMul m n = (\s z -> m (n s) z)

churchPow :: Cnum a -> (Cnum a -> Cnum a) -> Cnum a
churchPow m n = n m
