{-# OPTIONS --cubical --safe #-}
module SymInt where

open import Cubical.Core.Everything
open import Cubical.HITs.HitInt renaming (_+ℤ_ to _+_; ℤ to Z)
open import Cubical.Data.Nat using (suc)


+-i-zero : ∀ a i → posneg i + a ≡ a
+-i-zero (pos 0) i j = posneg (i ∧ ~ j)
+-i-zero (pos (suc n)) i j = sucℤ (+-i-zero (pos n) i j)
+-i-zero (neg 0) i j = posneg (i ∨ j)
+-i-zero (neg (suc n)) i j = predℤ (+-i-zero (neg n) i j)
+-i-zero (posneg k) i j = posneg ((i ∧ ~ j) ∨ (i ∨ j) ∧ k)
