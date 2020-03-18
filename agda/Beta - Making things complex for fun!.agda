{-# OPTIONS --safe #-}

open import Preloaded
open ≡-Reasoning

module PainfulNat 
  (fun-ext : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g) where


pzero : Painfulℕ
pzero = pain true λ ()

psuc : Painfulℕ → Painfulℕ
psuc n = pain false λ {refl → n}

_p+_ : Painfulℕ → Painfulℕ → Painfulℕ
pain true  _  p+ n = n
pain false fm p+ n = psuc (fm refl p+ n)

+-passoc : ∀ m n p → (m p+ n) p+ p ≡ m p+ (n p+ p)
+-passoc (pain true _)   _ _ = refl
+-passoc (pain false fm) n p = cong psuc (+-passoc (fm refl) n p)

pzero-same : ∀ {p} → pzero ≡ pain true p
pzero-same = cong (pain true) (fun-ext (λ ()))

+-pzero : ∀ n → n p+ pzero ≡ n
+-pzero (pain true _)   = pzero-same
+-pzero (pain false fn) = cong (pain false) (fun-ext λ {refl → +-pzero (fn refl)})

+-psuc : ∀ m n → m p+ psuc n ≡ psuc (m p+ n)
+-psuc (pain true _)   _ = refl
+-psuc (pain false fm) n = cong psuc (+-psuc (fm refl) n)

+-pcomm : ∀ m n → m p+ n ≡ n p+ m
+-pcomm (pain true _)   n = sym (trans (cong (n p+_) (sym pzero-same)) (+-pzero n))
+-pcomm (pain false fm) n = sym (
  begin
    n p+ pain false fm
  ≡⟨ cong (λ fm → n p+ pain false fm) (fun-ext λ {refl → refl}) ⟩
    n p+ psuc (fm refl)
  ≡⟨ +-psuc n (fm refl) ⟩
    psuc (n p+ fm refl)
  ≡⟨ cong psuc (sym (+-pcomm (fm refl) n)) ⟩
    psuc (fm refl) p+ n
  ∎)

pain⇔ℕ : Painfulℕ ⇔ ℕ
pain⇔ℕ = Bijection to from to∘from from∘to
  where
    to : Painfulℕ → ℕ
    to (pain true _)   = zero
    to (pain false fn) = suc (to (fn refl))

    from : ℕ → Painfulℕ
    from zero    = pzero
    from (suc n) = psuc (from n)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from zero    = refl
    to∘from (suc n) = cong suc (to∘from n)

    from∘to : ∀ x → from (to x) ≡ x
    from∘to (pain true _)   = pzero-same
    from∘to (pain false fn) = cong (pain false) (fun-ext λ {refl → from∘to (fn refl)})
