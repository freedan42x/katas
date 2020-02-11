{-# OPTIONS --safe --sized-types #-}
module SizedCoin where

open import Data.Nat
open import Size


record Stream (A : Set) {i : Size} : Set where
  coinductive
  constructor _∷_
  field
    head : A
    tail : {j : Size< i} → Stream A {j}

ZipWith = ∀ {A B C : Set} {i j : Size} -> (A -> B -> C)
        -> Stream A {i} -> Stream B {i} -> Stream C {i}
Cofib  = {i : Size} → Stream ℕ {i}
Coones = {i : Size} → Stream ℕ {i}
