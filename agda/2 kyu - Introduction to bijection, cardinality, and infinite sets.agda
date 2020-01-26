{-# OPTIONS --safe #-}
module Iso-properties where

open import Relation.Nullary
open import Data.Empty
open import Function using (id; _∘_)
open import Iso
open ≡-Reasoning
open _⇔_


data Bool : Set where
  true false : Bool

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


⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl
  = Bijection id id
    (λ _ → refl)
    λ _ → refl

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym (Bijection A→B B→A A→B→A B→A→B)
  = Bijection B→A A→B B→A→B A→B→A

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans (Bijection A→B B→A A→B→A B→A→B) (Bijection B→C C→B B→C→B C→B→C)
  = Bijection (B→C ∘ A→B) (B→A ∘ C→B)
    (λ a → trans (cong B→A (B→C→B (A→B a))) (A→B→A a))
    λ b → trans (cong B→C (B→A→B (C→B b))) (C→B→C b)

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


ℕ⇔ℕ+1 : ℕ ⇔ ℕ+1
ℕ⇔ℕ+1
  = Bijection
    (λ {0 → null; (suc n) → nat n})
    (λ {null → 0; (nat n) → suc n})
    (λ {0 → refl; (suc _) → refl})
    λ {null → refl; (nat _) → refl}


even : ℕ → Bool
even 0 = true
even 1 = false
even (suc (suc n)) = even n

even-dbl : ∀ n → even (n * 2) ≡ true
even-dbl 0 = refl
even-dbl (suc n) = even-dbl n

even-not-odd : ∀ n → even (suc (n * 2)) ≢ true
even-not-odd 0 = λ ()
even-not-odd (suc n) = even-not-odd n

≠true : ∀ n → even n ≢ true → even n ≡ false
≠true zero ¬e = ⊥-elim (¬e refl)
≠true 1 _ = refl
≠true (suc (suc n)) ¬e = ≠true n ¬e

pred-odd : ∀ n → even n ≡ false → even (pred n) ≡ true
pred-odd 1 _ = refl
pred-odd (suc (suc (suc n))) e = pred-odd (suc n) e

even? : ∀ n → Dec (even n ≡ true)
even? 0 = yes refl
even? 1 = no (λ ())
even? (suc (suc n)) = even? n

div2 : ∀ n → even n ≡ true → ℕ
div2 0 _ = 0
div2 (suc (suc n)) e = suc (div2 n e)

div2-sqr : ∀ n {e} → div2 (n * 2) e ≡ n
div2-sqr 0 = refl
div2-sqr (suc n) = cong suc (div2-sqr n)

div2*2 : ∀ n {e} → div2 n e * 2 ≡ n
div2*2 0 = refl
div2*2 (suc (suc n)) = cong (suc ∘ suc) (div2*2 n)

div2*2+1 : ∀ n {e : even n ≡ false} → suc (div2 (pred n) (pred-odd n e) * 2) ≡ n
div2*2+1 1 = refl
div2*2+1 (suc n) = cong suc (div2*2 n)

to : ℕ → ℕ+ℕ
to n with even? n
... | yes e = left (div2 n e)
... | no ¬e = right (div2 (pred n) (pred-odd n (≠true n ¬e)))

from : ℕ+ℕ → ℕ
from (left n) = n * 2
from (right n) = suc (n * 2)

from-to : ∀ n → from (to n) ≡ n
from-to n with even? n
... | yes e = div2*2 n
... | no ¬e = div2*2+1 n

to-from : ∀ n → to (from n) ≡ n
to-from (left n) with even? (n * 2)
... | yes _ = cong left (div2-sqr n)
... | no ¬e = ⊥-elim (¬e (even-dbl n))
to-from (right n) with even? (suc (n * 2))
... | yes e = ⊥-elim (even-not-odd n e)
... | no  _ = cong right (div2-sqr n)

ℕ⇔ℕ+ℕ : ℕ ⇔ ℕ+ℕ
ℕ⇔ℕ+ℕ
  = Bijection
   to
   from
   from-to
   to-from
