{-# OPTIONS --safe #-}
module Uneval where

open import Agda.Builtin.Reflection

open import Eval

open import Data.Unit
open import Data.List using ([]; _∷_)


uwu : Term → Term
uwu (con (quote zero) []) = con (quote !zro) []
uwu (con (quote suc) (arg i x ∷ [])) =
  con (quote !suc) (arg i (uwu x) ∷ [])
uwu (def (quote _+_) (arg i x ∷ arg j y ∷ [])) =
  con (quote _!+_) (arg i (uwu x) ∷ arg j (uwu y) ∷ [])
uwu (def (quote _*_) (arg i x ∷ arg j y ∷ [])) =
  con (quote _!*_) (arg i (uwu x) ∷ arg j (uwu y) ∷ [])
uwu n = con (quote !lit)
  ((arg (arg-info visible relevant) n ∷ []))

macro
  parseℕ : Term → Term → TC ⊤
  parseℕ t hole = unify hole (uwu t)
