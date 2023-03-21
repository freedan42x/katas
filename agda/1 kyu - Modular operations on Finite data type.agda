{-# OPTIONS --safe #-}
module Mod where

open import Data.Fin
open import Data.Nat as ℕ
  using (ℕ; zero; suc; z≤n; s≤s)

private variable k : ℕ


last : Fin (suc k)
last {k = zero} = zero
last {k = suc _} = suc last

negate : Fin k → Fin k
negate zero = zero
negate (suc zero) = last
negate (suc n) = inject₁ (negate n)

dec : Fin k → Fin k
dec zero = last
dec (suc n) = inject₁ n

subt : Fin k → Fin k → Fin k
subt {suc k} m n = fold (λ _ → Fin (suc k)) dec m n

inc : Fin k → Fin k
inc {suc zero} n = n
inc {suc (suc _)} n = subt n (negate (suc zero))

add : Fin k → Fin k → Fin k
add {suc k} m n = fold (λ _ → Fin (suc k)) inc n m

mult : Fin k → Fin k → Fin k
mult {suc k} m n = fold (λ _ → Fin (suc k)) (add n) zero m
