{-# OPTIONS --safe #-}
module PerfectSquare where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


expand : ∀ n -> (n + 1) ^ 2 ≡ n ^ 2 + 2 * n + 1
expand n = begin
  (n + 1) ^ 2               ≡⟨ (n + 1) ^2 ⟩
  (n + 1) * (n + 1)         ≡⟨ *-distribˡ-+ (n + 1) n 1 ⟩
  (n + 1) * n + (n + 1) * 1 ≡⟨ cong ((n + 1) * n +_) (*-identityʳ (n + 1)) ⟩
  (n + 1) * n + (n + 1)     ≡⟨ cong (_+ (n + 1)) (*-distribʳ-+ n n 1) ⟩
  n * n + (n + 0) + (n + 1) ≡⟨ cong (λ x → n * n + x + (n + 1)) (+-identityʳ n) ⟩
  n * n + n + (n + 1)       ≡⟨ sym (+-assoc (n * n + n) n 1) ⟩
  n * n + n + n + 1         ≡⟨ cong (_+ 1) (+-assoc (n * n) n n) ⟩
  n * n + (n + n) + 1       ≡⟨ cong (λ x → n * n + x + 1) (sym (2* n)) ⟩
  n * n + 2 * n + 1         ≡⟨ cong (λ x → x + 2 * n + 1) (sym (n ^2)) ⟩
  n ^ 2 + 2 * n + 1         ∎
    where
      _^2 : ∀ n → n ^ 2 ≡ n * n
      n ^2 rewrite *-identityʳ n = refl

      2*_ : ∀ n → 2 * n ≡ n + n
      2* n rewrite +-identityʳ n = refl
