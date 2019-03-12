{-# OPTIONS --safe #-}

module AdHoc where

open import Relation.Binary.PropositionalEquality
open import Data.Char
open import Agda.Builtin.Char using (primCharEquality)
open import Agda.Builtin.String using (primStringEquality)
open import Data.String hiding (length)
open import Data.List
open import Data.Integer renaming (_≟_ to _ℤ≟_)
open import Data.Nat as N
open import Agda.Builtin.Nat using (_==_)
open import Data.Bool as B
open import Relation.Nullary.Decidable

record Eq (A : Set) : Set where
  field
    _==`_ : A → A → Bool

open Eq ⦃ ... ⦄

_===_ : ∀ {A} ⦃ eq : Eq A ⦄ → A → A → Bool
x === y = x ==` y

_=/=_ : ∀ {A} ⦃ eq : Eq A ⦄ → A → A → Bool
x =/= y = not (x === y)

c-𝔹 : Bool → Bool → Bool
c-𝔹 true  b = b
c-𝔹 false b = not b

eqList : ∀ {A : Set} ⦃ eq : Eq A ⦄ → List A → List A → Bool
eqList [] [] = true
eqList [] (y ∷ ys) = false
eqList (x ∷ xs) [] = false
eqList (x ∷ xs) (y ∷ ys) with x === y
... | true  = eqList xs ys
... | false = false

instance
  EqBool : Eq Bool
  EqBool = record { _==`_ = c-𝔹 }

  Eqℕ : Eq ℕ
  Eqℕ = record { _==`_ = _==_ }

  EqChar : Eq Char
  EqChar = record { _==`_ = primCharEquality }

  EqString : Eq String
  EqString = record { _==`_ = primStringEquality }

  Eqℤ : Eq ℤ
  Eqℤ = record { _==`_ = λ x y → ⌊ x ℤ≟ y ⌋ }

  EqList : ∀ {A : Set} ⦃ EqA : Eq A ⦄ → Eq (List A)
  EqList = record { _==`_ = eqList }
