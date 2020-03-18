{-# OPTIONS --safe #-}
module Solution where

open import Preloaded
open import Data.List
open import Data.Nat
open import Data.Empty
open import Data.Bool hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


subseq-match⇒subseq : ∀ xs ys → subseq-match xs ys ≡ true → Subseq xs ys
subseq-match⇒subseq [] [] refl = subseq-nil
subseq-match⇒subseq [] (y ∷ ys) refl =
  subseq-drop y [] ys (subseq-match⇒subseq [] ys refl)
subseq-match⇒subseq (x ∷ xs) (y ∷ ys) p with x ≟ y
... | yes refl =
  subseq-take x xs ys (subseq-match⇒subseq xs ys p)
... | no _ =
  subseq-drop y (x ∷ xs) ys (subseq-match⇒subseq (x ∷ xs) ys p)

subseq⇒subseq-match : ∀ xs ys → Subseq xs ys → subseq-match xs ys ≡ true
subseq⇒subseq-match [] _ _ = refl
subseq⇒subseq-match (x ∷ xs) (y ∷ ys) s with x ≟ y
... | yes refl = subseq⇒subseq-match xs ys (subseq-drop2 s)
  where
    subseq-drop2 : ∀ {xs ys x y} → Subseq (x ∷ xs) (y ∷ ys) → Subseq xs ys
    subseq-drop2 (subseq-take _ _ _ s) = s
    subseq-drop2 (subseq-drop _ (_ ∷ xs) (y ∷ ys) s) =
      subseq-drop y xs ys (subseq-drop2 s)
subseq⇒subseq-match (_ ∷ _) (_ ∷ _) (subseq-take _ _ _ _)
  | no oh = ⊥-elim (oh refl)
subseq⇒subseq-match (x ∷ xs) (_ ∷ ys) (subseq-drop _ .(x ∷ xs) .ys s)
  | no _ = subseq⇒subseq-match (x ∷ xs) ys s
