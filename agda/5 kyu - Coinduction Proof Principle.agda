{-# OPTIONS --copattern --cubical --safe --no-sized-types --guardedness #-}
module CPP where

open import StreamDef
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

{-
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public

-- | Bisimulation as equality
record _==_ {A : Set} (x : Stream A) (y : Stream A) : Set where
  coinductive
  field
    refl-head : head x ≡ head y
    refl-tail : tail x == tail y
open _==_ public
-}


path≡bisim : {A : Set} → {x y : Stream A} → (x ≡ y) ≡ (x == y)
path≡bisim = isoToPath (iso to from to∘from from∘to)
  where
    to : ∀ {x y} → x ≡ y → x == y
    refl-head (to p) = cong head p
    refl-tail (to p) = to (cong tail p)

    from : ∀ {x y} → x == y → x ≡ y
    head (from p i) = refl-head p i
    tail (from p i) = from (refl-tail p) i

    to∘from : ∀ {x y} (p : x == y) → to (from p) ≡ p
    refl-head (to∘from p _) = refl-head p
    refl-tail (to∘from p i) = to∘from (refl-tail p) i

    from∘to : ∀ {x y} (p : x ≡ y) → from (to p) ≡ p
    head (from∘to p _ j) = head (p j)
    tail (from∘to p i j) = from∘to (cong tail p) i j
