{-# OPTIONS --safe #-}
module OddsAndEvens where

open import Preloaded
open import Data.Nat

{- Preloaded code:

data Even : ℕ → Set
data Odd  : ℕ → Set

data Even where
  zero : Even zero
  suc  : ∀ {n : ℕ} → Odd n → Even (suc n)

data Odd where
  suc : ∀ {n : ℕ} → Even n → Odd (suc n)
  
-}

-- | Implement all these functions
infixl 6 _e+e_ _o+e_ _o+o_ _e+o_
_e+e_ : ∀ {m n : ℕ} → Even m → Even n → Even (m + n)
_o+e_ : ∀ {m n : ℕ} → Odd  m → Even n → Odd  (m + n)
_o+o_ : ∀ {m n : ℕ} → Odd  m → Odd  n → Even (m + n)
_e+o_ : ∀ {m n : ℕ} → Even m → Odd  n → Odd  (m + n)

zero e+e n  = n
suc m e+e n = suc (m o+e n)

suc m o+e n = suc (m e+e n)
suc m o+o n = suc (m e+o n)

zero e+o n  = n
suc m e+o n = suc (m o+o n)
