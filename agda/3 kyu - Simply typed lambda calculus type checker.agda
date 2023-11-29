{-# OPTIONS --safe #-}
module LambdaCalculusTypeChecker where

open import LambdaCalculus
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String hiding (show)
open import Data.Sum
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.List hiding (_++_)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Nat.Show

{- Preloaded
open import Data.Product
open import Data.List
open import Function

Name = Nat

infixr 7 _=>_
data Type : Set where
  nat  : Type
  _=>_ : Type -> Type -> Type
private variable a b c d : Type

Ctx = List (Name × Type)
variable Γ : Ctx

infix 4 _∈_
data _∈_ {A : Set} (a : A) : List A -> Set where
  emm : (as : List A) -> a ∈ a ∷ as
  hmm : ∀ {as c} -> (a ∈ as) -> a ∈ c ∷ as

module Untyped where
  data Term : Set where
    var : Name -> Term
    lit : Nat  -> Term
    suc : Term
    app : Term -> Term -> Term
    lam : Name -> Type -> Term -> Term

module Typed where
  data Term (Γ : Ctx) : Type -> Set where
    var : ∀ {a} (x : Name) (i : (x , a) ∈ Γ) -> Term Γ a
    lit : (n : Nat) -> Term Γ nat
    suc : Term Γ (nat => nat)
    app : Term Γ (a => b) -> Term Γ a -> Term Γ b
    lam : (x : Name) (a : Type) -> Term ((x , a) ∷ Γ) b
        -> Term Γ (a => b)

module Erase where
  open Typed public
  open Untyped renaming (Term to Expr) public

  eraseType : Term Γ a -> Expr
  eraseType (var x _) = var x
  eraseType (lit n) = lit n
  eraseType suc = suc
  eraseType (app f x) = app (eraseType f) $ eraseType x
  eraseType (lam x t e) = lam x t $ eraseType e

TypeError = String
TCM : Set -> Set
TCM A = TypeError ⊎ A

data Success (Γ : Ctx) : Untyped.Term -> Set where
  ok : ∀ a (v : Typed.Term Γ a) -> Success Γ (Erase.eraseType v)

-}

module TypeCheck where
  open Erase

  eqType : (a b : Type) → Maybe (a ≡ b)
  eqType nat nat = just refl
  eqType nat (_ => _) = nothing
  eqType (_ => _) nat = nothing
  eqType (a => b) (a₁ => b₁) with eqType a a₁ | eqType b b₁
  ... | just refl | just refl = just refl
  ... | _ | _ = nothing

  ctxContains : (x : Nat) (Γ : Ctx) → Maybe (∃ λ t → (x , t) ∈ Γ)
  ctxContains _ [] = nothing
  ctxContains x ((y , t) ∷ xs) with x Data.Nat.≟ y
  ... | yes refl = just (t , emm xs)
  ... | no k = Data.Maybe.map (Data.Product.map₂ hmm) (ctxContains x xs)

  typeCheck : (Γ : Ctx) (e : Expr) -> TCM (Success Γ e)
  typeCheck Γ (var x) with ctxContains x Γ
  ... | just (t , proof) = inj₂ (ok t (var x proof))
  ... | nothing = inj₁ ("Variable out of scope: " ++ show x)

  typeCheck _ (lit x) = inj₂ (ok nat (lit x))

  typeCheck _ suc = inj₂ (ok (nat => nat) suc)

  typeCheck Γ (app f x) with typeCheck Γ f
  ... | inj₁ err = inj₁ err
  ... | inj₂ (ok nat _) = inj₁ "Nat is not a function!"
  ... | inj₂ (ok (arg => r) v₁) with typeCheck Γ x
  ... | inj₁ err = inj₁ err
  ... | inj₂ (ok a v₂) with eqType arg a
  ... | just refl = inj₂ (ok r (app v₁ v₂))
  ... | nothing = inj₁ "Argument type mismatch!"

  typeCheck Γ (lam x t e) with typeCheck ((x , t) ∷ Γ) e
  ... | inj₁ err = inj₁ err
  ... | inj₂ (ok a v) = inj₂ (ok (t => a) (lam x t v))
