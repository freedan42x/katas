{-# OPTIONS --safe #-}
module Iso-properties where

open import Relation.Nullary
open import Data.Empty
open import Function using (id; _∘_)
open import Iso
open ≡-Reasoning
open _⇔_

-- Task 0 : Example of _⇔_ in finite sets
-- Task 0-1. Find a bijection between Bool and Bit. (provided for you as an example)
data Bool : Set where
  true false : Bool

omni-elim : ∀ {x} → x ≡ true → x ≡ false → ⊥
omni-elim {true} _ ()
omni-elim {false} () _

data Bit : Set where
  0b 1b : Bit

Bool→Bit : Bool → Bit
Bool→Bit false = 0b
Bool→Bit true = 1b

Bit→Bool : Bit → Bool
Bit→Bool 0b = false
Bit→Bool 1b = true

Bool→Bit→Bool : ∀ (b : Bool) → Bit→Bool (Bool→Bit b) ≡ b
Bool→Bit→Bool true = refl
Bool→Bit→Bool false = refl

Bit→Bool→Bit : ∀ (b : Bit) → Bool→Bit (Bit→Bool b) ≡ b
Bit→Bool→Bit 0b = refl
Bit→Bool→Bit 1b = refl

Bool⇔Bit : Bool ⇔ Bit
Bool⇔Bit = Bijection Bool→Bit Bit→Bool Bool→Bit→Bool Bit→Bool→Bit

--------------------------------------------------------------------
-- Task 1 : General properties of ⇔
-- Task 1-1. Prove that any set has the same cardinality as itself.
⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl
  = Bijection id id
    (λ _ → refl)
    λ _ → refl

-- Task 1-2. Prove that _⇔_ relation is symmetric.
⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym (Bijection A→B B→A A→B→A B→A→B)
  = Bijection B→A A→B B→A→B A→B→A

-- Task 1-3. Prove that _⇔_ relation is transitive.
⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans (Bijection A→B B→A A→B→A B→A→B) (Bijection B→C C→B B→C→B C→B→C)
  = Bijection (B→C ∘ A→B) (B→A ∘ C→B)
    (λ a → trans (cong B→A (B→C→B (A→B a))) (A→B→A a))
    λ b → trans (cong B→C (B→A→B (C→B b))) (C→B→C b)

-- Task 1-4. Prove the following statement:
--   Given two functions A→B and B→A, if A→B→A is satisfied and B→A is injective, A ⇔ B.
bijection-alt :
  ∀ {A B : Set} →
  (A→B : A → B) →
  (B→A : B → A) →
  (∀ a → B→A (A→B a) ≡ a) →
  (∀ b b' → B→A b ≡ B→A b' → b ≡ b') →
  A ⇔ B
bijection-alt A→B B→A A→B→A B→A-inj
  = Bijection A→B B→A A→B→A
    λ b → B→A-inj (A→B (B→A b)) b (A→B→A (B→A b))

--------------------------------------------------------------------
-- Task 2 : ⇔-relations between ℕ and various supersets of ℕ

-- ℕ+1 : A set having one more element than ℕ.
{- Preloaded code
data ℕ+1 : Set where
  null : ℕ+1
  nat : ℕ → ℕ+1
-}

-- Task 2-1. Prove that ℕ has the same cardinality as ℕ+1.
ℕ⇔ℕ+1 : ℕ ⇔ ℕ+1
ℕ⇔ℕ+1
  = Bijection
    (λ {zero → null; (suc n) → nat n})
    (λ {null → zero; (nat n) → suc n})
    (λ {zero → refl; (suc _) → refl})
    λ {null → refl; (nat _) → refl}

-- ℕ+ℕ : A set having size(ℕ) more elements than ℕ.
{- Preloaded code
data ℕ+ℕ : Set where
  left : ℕ → ℕ+ℕ
  right : ℕ → ℕ+ℕ
-}

even : ℕ → Bool
even zero = true
even 1 = false
even (suc (suc n)) = even n

even? : ∀ n → Dec (even n ≡ true)
even? zero = yes refl
even? 1 = no (λ ())
even? (suc (suc n)) = even? n

even-doubled : ∀ n → even (n * 2) ≡ true
even-doubled zero = refl
even-doubled (suc n) = even-doubled n

n*2+1≠even : ∀ n → ¬ even (suc (n * 2)) ≡ true
n*2+1≠even zero ()
n*2+1≠even (suc n) p = n*2+1≠even n p

div2 : ∀ n → even n ≡ true → ℕ
div2 zero _ = zero
div2 1 ()
div2 (suc (suc n)) p = suc (div2 n p)

help : ∀ x → x ≢ true → x ≡ false
help true ¬x = ⊥-elim (¬x refl)
help false _ = refl

heelp : ∀ n → ¬ even n ≡ true → even n ≡ false
heelp n ¬e with even? n
... | yes e = ⊥-elim (¬e e)
... | no _  = help (even n) ¬e

heeelp : ∀ n → even n ≡ false → even (suc n) ≡ true
heeelp 1 _ = refl
heeelp (suc (suc n)) b = heeelp n b

heeeelp : ∀ n → even n ≡ false → even (pred n) ≡ true
heeeelp 1 _ = refl
heeeelp (suc (suc n)) b = heeelp n b

div2*2 : ∀ n (e : even n ≡ true) → div2 n e * 2 ≡ n
div2*2 zero _ = refl
div2*2 (suc (suc n)) e = cong (suc ∘ suc) (div2*2 n e)

div2-sqr : ∀ n {e} → div2 (n * 2) e ≡ n
div2-sqr zero = refl
div2-sqr (suc n) = cong suc (div2-sqr n)

div2*2+1-helper : ∀ n e → div2 n (heeelp (suc n) e) * 2 ≡ n
div2*2+1-helper zero _ = refl
div2*2+1-helper (suc (suc n)) e = cong (suc ∘ suc) (div2*2+1-helper n e)

div2*2+1 : ∀ n (e : even n ≡ false) → suc (div2 (pred n) (heeeelp n e) * 2) ≡ n
div2*2+1 1 _ = refl
div2*2+1 (suc (suc (suc n))) e = cong (suc ∘ suc ∘ suc) (div2*2+1-helper n e)

to : ℕ → ℕ+ℕ
to n with even? n
... | yes e = left (div2 n e)
... | no ¬e = right (div2 (pred n) (heeeelp n (heelp n ¬e)))

from : ℕ+ℕ → ℕ
from (left n) = n * 2
from (right n) = suc (n * 2)

from-to : (n : ℕ) → from (to n) ≡ n
from-to n with even? n
... | yes e = div2*2 n e
... | no ¬e = div2*2+1 n (heelp n ¬e)

to-from : (n : ℕ+ℕ) → to (from n) ≡ n
to-from (left n) with even? (n * 2)
... | yes _ = cong left (div2-sqr n)
... | no ¬e = ⊥-elim (¬e (even-doubled n))
to-from (right zero) = refl
to-from (right n) with even? (suc (n * 2))
... | yes e = ⊥-elim (n*2+1≠even n e)
... | no ¬e = cong right (div2-sqr n)

-- -- Task 2-2. Prove that ℕ has the same cardinality as ℕ+ℕ.
ℕ⇔ℕ+ℕ : ℕ ⇔ ℕ+ℕ  -- I am an idiot.
ℕ⇔ℕ+ℕ
  = Bijection
   to
   from
   from-to
   to-from
