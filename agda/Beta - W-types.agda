{-# OPTIONS --cubical --safe #-}
module Solution where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Everything
open import Data.List
open import Preloaded

{- Proloaded:
data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (B a → W A B) → W A B

ℕᵂ : Set
ℕᵂ = W Bool λ {false → ⊥ ; true → Unit}

Listᵂ : Set → Set
Listᵂ A = W (Unit ⊎ A) λ {(inl _) → ⊥ ; (inr _)   → Unit}
-}

ℕ≡ℕᵂ : ℕ ≡ ℕᵂ
ℕ≡ℕᵂ = isoToPath (iso to from to∘from from∘to)
  where
    to : ℕ → ℕᵂ
    to zero = sup false λ ()
    to (suc n) = sup true λ _ → to n

    from : ℕᵂ → ℕ
    from (sup false _) = zero
    from (sup true w) = suc (from (w tt))

    to∘from : ∀ w → to (from w) ≡ w
    to∘from (sup false w) = cong (sup false) (funExt λ ())
    to∘from (sup true w) = cong (sup true) λ i _ → to∘from (w tt) i

    from∘to : ∀ n → from (to n) ≡ n
    from∘to zero = refl
    from∘to (suc n) = cong suc (from∘to n)


List≡Listᵂ : ∀ {A} → List A ≡ Listᵂ A
List≡Listᵂ {A} = isoToPath (iso to from to∘from from∘to)
  where
    to : List A → Listᵂ A
    to [] = sup (inl tt) λ ()
    to (x ∷ xs) = sup (inr x) λ _ → to xs

    from : Listᵂ A → List A
    from (sup (inl _) _) = []
    from (sup (inr x) w) = x ∷ from (w tt)

    to∘from : ∀ w → to (from w) ≡ w
    to∘from (sup (inl tt) _) = cong (sup (inl tt)) (funExt λ ())
    to∘from (sup (inr x) w) = cong (sup (inr x)) (funExt (λ _ i → to∘from (w tt) i))

    from∘to : ∀ xs → from (to xs) ≡ xs
    from∘to [] = refl
    from∘to (x ∷ xs) = cong (x ∷_) (from∘to xs)
