{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module IdentitySort where

import           Data.Kind

data Z
data S n

data Natural :: Type -> Type where
  NumZ ::Natural Z
  NumS ::Natural n -> Natural (S n)

type family LessOrEq m n where
  LessOrEq Z _ = 'True
  LessOrEq (S _) Z = 'False
  LessOrEq (S m) (S n) = LessOrEq m n

type family LessOrEqList n xs where
  LessOrEqList n '[] = 'True
  LessOrEqList n (x ': _) = LessOrEq n x

data SortedList :: [Type] -> Type where
  Nil ::SortedList '[]
  Cons ::(LessOrEqList n ns ~ 'True) => Natural n -> SortedList ns -> SortedList (n ': ns)

identitySort :: SortedList n -> SortedList n
identitySort x = x
