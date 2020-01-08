{-# OPTIONS --safe #-}
module Sprintf where

open import Data.Char
open import Data.Integer renaming (show to showℤ)
open import Data.Float renaming (show to show𝔽)
open import Data.String
open import Data.List hiding (_++_)
open import Function


data Format : Set where
  %c %% : Format → Format
  %d    : Format → Format
  %f    : Format → Format
  other : Char   → Format → Format
  end   : Format

format : String → Format
format = f ∘ toList where
  f : List Char → Format
  f [] = end
  f ('%' ∷ 'c' ∷ xs) = %c $ f xs
  f ('%' ∷ '%' ∷ xs) = %% $ f xs
  f ('%' ∷ 'd' ∷ xs) = %d $ f xs
  f ('%' ∷ 'f' ∷ xs) = %f $ f xs
  f (x ∷ xs) = other x $ f xs

typify : Format → Set
typify (%c f) = Char → typify f
typify (%% f) = typify f
typify (%d f) = ℤ → typify f
typify (%f f) = Float → typify f
typify (other _ f) = typify f
typify end = String

to-func : ∀ f → String → typify f
to-func (%c f) s = λ c → to-func f $ s ++ fromList [ c ]
to-func (%% f) s = to-func f $ s ++ "%"
to-func (%d f) s = λ z → to-func f $ s ++ showℤ z
to-func (%f f) s = λ d → to-func f $ s ++ show𝔽 d
to-func (other x f) s = to-func f $ s ++ fromList [ x ]
to-func end s = s

sprintf : ∀ s -> typify (format s)
sprintf s = to-func (format s) ""
