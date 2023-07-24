{-# OPTIONS --safe #-}
module IncompleteIso where

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Preloaded

{- Preloaded
record IsIsomorphism {A B : Set} (f : A → B) (g : B → A) : Set where
  constructor IsIso
  field
    section : ∀ (a : A) → g (f a) ≡ a
    retract : ∀ (b : B) → f (g b) ≡ b
-}

nope : 0 ≡ 1 → ⊥
nope ()

noIncompleteIso : ¬ ({A B : Set} (f : A → B) (g : B → A) → (∀ (a : A) → g (f a) ≡ a) → IsIsomorphism f g)
noIncompleteIso = λ p →
  let IsIso _ r = p (λ {tt → zero}) (λ _ → tt) λ {tt → refl}
  in nope (r 1)
