{-# OPTIONS --safe #-}
module ArithSeq where

open import Data.Nat
open import Data.Nat.Properties hiding (*-suc)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Preloaded


*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc zero    n = refl
*-suc (suc m) n = begin
  suc m * suc n         ≡⟨⟩
  suc n + m * suc n     ≡⟨ cong (suc n +_) (*-suc m n) ⟩
  suc n + (m + m * n)   ≡⟨⟩
  suc (n + (m + m * n)) ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
  suc (n + m + m * n)   ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m) ⟩
  suc (m + n + m * n)   ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
  suc (m + (n + m * n)) ≡⟨⟩
  suc m + suc m * n     ∎

*2/2 : ∀ m n → ⌊ m + m + n /2⌋ ≡ m + ⌊ n /2⌋
*2/2 zero n = refl
*2/2 (suc m) n rewrite +-identityʳ m =
  begin
    ⌊ suc m + suc m + n /2⌋
  ≡⟨ cong (λ x → ⌊ x + n /2⌋) (+-suc (suc m) m) ⟩
    suc ⌊ m + m + n /2⌋
  ≡⟨ cong suc (*2/2 m n) ⟩
    suc (m + ⌊ n /2⌋)
  ∎

arith-eq : (n : ℕ) -> arith-formula n ≡ arith-sum n
arith-eq zero = refl
arith-eq (suc n) =
  begin
    ⌊ suc n + 1 + n * suc (n + 1) /2⌋
  ≡⟨ cong (λ x → ⌊ x + n * suc (n + 1) /2⌋) (+-comm (suc n) 1) ⟩
    suc ⌊ n + n * suc (n + 1) /2⌋
  ≡⟨ cong (λ x → suc ⌊ n + x /2⌋) (*-suc n (n + 1)) ⟩
    suc ⌊ n + (n + n * (n + 1)) /2⌋
  ≡⟨ cong (λ x → suc ⌊ x /2⌋) (sym (+-assoc n n (n * (n + 1)))) ⟩
    suc ⌊ n + n + n * (n + 1) /2⌋
  ≡⟨ cong suc (*2/2 n (n * (n + 1))) ⟩
    suc n + ⌊ n * (n + 1) /2⌋
  ≡⟨ cong (suc n +_) (arith-eq n) ⟩
    suc n + arith-sum n
  ∎
