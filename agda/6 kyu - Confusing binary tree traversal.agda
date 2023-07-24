{-# OPTIONS --safe #-}
module Solution where

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Data.List
open import Data.List.Properties
open import Data.Sum
open import Data.Product
open import Preloaded

flip : ∀ {a} {A : Set a} (t : Tree A) → Tree A
flip (leaf n) = leaf n
flip (branch l r) = branch r l

join : ∀ {a} {A : Set a} (t₁ t₂ : Tree A) → Tree A
join t₁ t₂ = branch t₁ (flip t₂)

split : ∀ {a} {A : Set a} (t : Tree A) → A ⊎ (Tree A × Tree A)
split (leaf n) = inj₁ n
split (branch t₁ t₂) = inj₂ (t₁ , flip t₂)

lemma₁ : ∀ {a} {A : Set a} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
lemma₁ [] ys = sym (++-identityʳ (reverse ys))
lemma₁ (x ∷ xs) ys =
  begin
    reverse (x ∷ (xs ++ ys))
  ≡⟨ unfold-reverse x (xs ++ ys) ⟩
    reverse (xs ++ ys) ∷ʳ x
  ≡⟨ cong (_∷ʳ x) (lemma₁ xs ys) ⟩
    (reverse ys ++ reverse xs) ∷ʳ x
  ≡⟨ ++-assoc (reverse ys) (reverse xs) (x ∷ []) ⟩
    reverse ys ++ reverse xs ++ x ∷ []
  ≡⟨ cong (reverse ys ++_) (sym (unfold-reverse x xs)) ⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

lemma₂ : ∀ {a} {A : Set a} (t : Tree A) → reverse (to-list-rev t) ≡ to-list t
lemma₃ : ∀ {a} {A : Set a} (t : Tree A) → reverse (to-list t) ≡ to-list-rev t
lemma₂ (leaf n) = refl
lemma₂ (branch l r) =
  begin
    reverse (to-list r ++ to-list-rev l)
  ≡⟨ lemma₁ (to-list r) (to-list-rev l) ⟩
    reverse (to-list-rev l) ++ reverse (to-list r)
  ≡⟨ cong (_++ reverse (to-list r)) (lemma₂ l) ⟩
    to-list l ++ reverse (to-list r)
  ≡⟨ cong (to-list l ++_) (lemma₃ r) ⟩
    to-list l ++ to-list-rev r
  ∎

lemma₃ (leaf n) = refl
lemma₃ (branch l r) =
  begin
    reverse (to-list l ++ to-list-rev r)
  ≡⟨ lemma₁ (to-list l) (to-list-rev r) ⟩
    reverse (to-list-rev r) ++ reverse (to-list l)
  ≡⟨ cong (_++ reverse (to-list l)) (lemma₂ r) ⟩
    to-list r ++ reverse (to-list l)
  ≡⟨ cong (to-list r ++_) (lemma₃ l) ⟩
    to-list r ++ to-list-rev l
  ∎

to-list-flip : ∀ {a} {A : Set a} (t : Tree A) → to-list (flip t) ≡ reverse (to-list t)
to-list-flip (leaf n) = refl
to-list-flip (branch l r) = sym (
  begin
    reverse (to-list l ++ to-list-rev r)
  ≡⟨ lemma₁ (to-list l) (to-list-rev r) ⟩
    reverse (to-list-rev r) ++ reverse (to-list l)
  ≡⟨ cong (_++ reverse (to-list l)) (lemma₂ r) ⟩
    to-list r ++ reverse (to-list l)
  ≡⟨ cong (to-list r ++_) (lemma₃ l) ⟩
    to-list r ++ to-list-rev l
  ∎)

lemma₄ : ∀ {a} {A : Set a} (t : Tree A) → to-list-rev (flip t) ≡ to-list t
lemma₄ (leaf n) = refl
lemma₄ (branch l r) = refl

to-list-join : ∀ {a} {A : Set a} (t₁ t₂ : Tree A) → to-list (join t₁ t₂) ≡ to-list t₁ ++ to-list t₂
to-list-join t₁ t₂ = cong (to-list t₁ ++_) (lemma₄ t₂)

flip-involutive : ∀ {a} {A : Set a} (t : Tree A) → t ≡ flip (flip t)
flip-involutive (leaf n) = refl
flip-involutive (branch t₁ t₂) = refl

split-leaf-join : ∀ {a} {A : Set a} (t : Tree A) →
  [ (λ n → t ≡ leaf n) , (λ { (a , b) → t ≡ join a b }) ]′ (split t)
split-leaf-join (leaf n) = refl
split-leaf-join (branch t₁ t₂) = cong (branch t₁) (flip-involutive t₂)
