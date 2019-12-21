{-# OPTIONS --safe #-}
module Proof where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

invert : (a b : ℕ) → a + a ≡ b + b → a ≡ b
invert zero zero proof = refl
invert zero (suc _) ()
invert (suc a) zero ()
invert (suc a) (suc b) proof =
  cong suc (
    invert a b (
      cong pred (
        trans (+-comm (suc a) a)(
        trans (cong pred proof)(
        +-comm b (suc b)
        )))))
