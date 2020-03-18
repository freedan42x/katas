{-# OPTIONS --safe #-}
module Sum where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Preloaded
open ≡-Reasoning


lemma : ∀ f x n → sumAux x f n ≡ x + sumTail f n
lemma f x zero rewrite +-identityʳ (f zero) = +-comm (f zero) x
lemma f x (suc n) rewrite +-identityʳ (f (suc n)) =
  begin
    sumAux (f (suc n) + x) f n
  ≡⟨ lemma f (f (suc n) + x) n ⟩
    f (suc n) + x + sumTail f n
  ≡⟨ cong (_+ sumTail f n) (+-comm (f (suc n)) x) ⟩
    x + f (suc n) + sumTail f n
  ≡⟨ +-assoc x (f (suc n)) (sumTail f n) ⟩
    x + (f (suc n) + sumTail f n)
  ≡⟨ cong (x +_) (sym (lemma f (f (suc n)) n)) ⟩
    x + sumAux (f (suc n)) f n
  ∎

sumEq : (f : ℕ → ℕ) → (n : ℕ) → sumTail f n ≡ sumSimple f n
sumEq f zero rewrite +-identityʳ (f zero) = refl
sumEq f (suc n) rewrite +-identityʳ (f (suc n)) =
  begin
    sumAux (f (suc n)) f n
  ≡⟨ lemma f (f (suc n)) n ⟩
    f (suc n) + sumTail f n
  ≡⟨ cong (f (suc n) +_) (sumEq f n) ⟩
    f (suc n) + sumSimple f n
  ∎
