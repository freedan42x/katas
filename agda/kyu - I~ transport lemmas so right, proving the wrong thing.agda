{-# OPTIONS --cubical --safe #-}
module ProvingTheWrongThing where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Empty

theWrongThing : 1 + 1 ≡ 3 → ⊥
theWrongThing 2=3 = transport (cong ξ 2=3) tt
  where
    ξ : ℕ → Set
    ξ 2 = Unit
    ξ _ = ⊥
