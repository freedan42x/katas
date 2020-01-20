{-# OPTIONS --safe #-}
module RevRev where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.List
open import Data.List.Properties
open import Rev

{-
What you've just imported:

-- With this definition, Agda deduces better
rev : ∀ {ℓ} {A : Set ℓ} → List A → List A
rev [] = []
rev (x ∷ xs) = rev xs ++ x ∷ [] 
-}

rev-comm
  : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) →
  rev (xs ++ ys) ≡ rev ys ++ rev xs
rev-comm [] ys = sym (++-identityʳ (rev ys))
rev-comm (x ∷ xs) ys =
  begin
    rev (xs ++ ys) ++ x ∷ []
  ≡⟨ cong (_++ x ∷ []) (rev-comm xs ys) ⟩
    (rev ys ++ rev xs) ++ x ∷ []
  ≡⟨ ++-assoc (rev ys) (rev xs) (x ∷ []) ⟩
    rev ys ++ rev xs ++ x ∷ []
  ∎

revrevid : ∀ {ℓ} {A : Set ℓ} (a : List A) → rev (rev a) ≡ a
revrevid [] = refl
revrevid (x ∷ xs) =
  begin
    rev (rev xs ++ x ∷ [])
  ≡⟨ rev-comm (rev xs) (x ∷ []) ⟩
    x ∷ rev (rev xs)
  ≡⟨ cong (x ∷_) (revrevid xs) ⟩
    x ∷ xs
  ∎
