module Tagless where

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Nullary.Decidable


record Language (r : Set → Set → Set) : Set₁ where
  field
    here   : ∀ {a h} → r (a × h) a
    before : ∀ {a h any} → r h a → r (any × h) a
    lambda : ∀ {a b h} → r (a × h) b → r h (a → b)
    apply  : ∀ {a b h} → r h (a → b) → (r h a → r h b)
    
    loop   : ∀ {a h} → r h (a → a) → r h a
  
    nat    : ∀ {h} → ℕ → r h ℕ
    add    : ∀ {h} → r h ℕ → r h ℕ → r h ℕ
    down   : ∀ {h} → r h ℕ → r h ℕ
    up     : ∀ {h} → r h ℕ → r h ℕ
    mult   : ∀ {h} → r h ℕ → r h ℕ → r h ℕ
    gte    : ∀ {h} → r h ℕ → r h ℕ → r h Bool
  
    bool   : ∀ {h} → Bool → r h Bool
    and    : ∀ {h} → r h Bool → r h Bool → r h Bool
    or     : ∀ {h} → r h Bool → r h Bool → r h Bool
    neg    : ∀ {h} → r h Bool → r h Bool
  
    ifte   : ∀ {a h} → r h Bool → r h a → r h a → r h a

open Language {{...}} public


{-# TERMINATING #-}
fix : ∀ {A : Set} → (A → A) → A
fix f = f (fix f)

liftM2 : {A B C : Set} → (B → B → C) → (f g : A → B) → A → C
liftM2 op f g x = op (f x) (g x)


record R (A B : Set) : Set where
  constructor r
  field
    unR : A → B
open R 

instance
  l : Language R
  here   ⦃ l ⦄             = r proj₁
  before ⦃ l ⦄ (r f)       = r $ f ∘ proj₂
  lambda ⦃ l ⦄ (r f)       = r λ h a → f (a , h) 
  apply  ⦃ l ⦄ (r f) (r g) = r λ h → f h (g h)

  loop   ⦃ l ⦄ (r f)       = r $ fix ∘ f

  nat    ⦃ l ⦄ n           = r (const n)
  add    ⦃ l ⦄ (r f) (r g) = r $ liftM2 _+_ f g
  down   ⦃ l ⦄ (r f)       = r (pred ∘ f)
  up     ⦃ l ⦄ (r f)       = r (suc ∘ f)
  mult   ⦃ l ⦄ (r f) (r g) = r $ liftM2 _*_ f g
  gte    ⦃ l ⦄ (r f) (r g) = r $ liftM2 ((⌊_⌋ ∘_) ∘ _≥?_) f g

  bool   ⦃ l ⦄ b           = r (const b)
  and    ⦃ l ⦄ (r f) (r g) = r $ liftM2 _∧_ f g
  or     ⦃ l ⦄ (r f) (r g) = r $ liftM2 _∨_ f g
  neg    ⦃ l ⦄ (r f)       = r (not ∘ f)

  ifte   ⦃ l ⦄ (r p) (r f) (r g)
    = r λ x → if p x then f x else g x


Term : Set → Set₁
Term a = ∀ {r h} {{l : Language r}} → r h a

interpret : ∀ {a : Set} → Term a → a
interpret t = unR t zero
