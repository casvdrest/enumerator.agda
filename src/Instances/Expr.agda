{-# OPTIONS --safe #-}

module Instances.Expr where

open import Data.Nat hiding (_≤_)
open import Data.Nat.Properties
open import Data.Bool hiding (_≤_ ; _≟_)

module _ where

  data Type : Set where
    𝕟 𝕓 : Type

  data Expr : Type → Set where 
    add  : Expr 𝕟 → Expr 𝕟 → Expr 𝕟
    and  : Expr 𝕓 → Expr 𝕓 → Expr 𝕓
    leq  : Expr 𝕟 → Expr 𝕟 → Expr 𝕓
    bool : Bool → Expr 𝕓
    nat  : ℕ → Expr 𝕟

  Value : Type → Set
  Value 𝕟 = ℕ
  Value 𝕓 = Bool

  variable
    t : Type

  _≤_ : ℕ → ℕ → Bool 
  zero  ≤ m     = true
  suc n ≤ zero  = false
  suc n ≤ suc m = n ≤ m

  eval : Expr t → Value t
  eval (add e₁ e₂) = eval e₁ + eval e₂
  eval (and e₁ e₂) = eval e₁ ∧ eval e₂
  eval (leq e₁ e₂) = eval e₁ ≤ eval e₂
  eval (bool b)    = b
  eval (nat n)     = n


module _ where

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  add-comm : ∀ e₁ e₂ → eval (add e₁ e₂) ≡ eval (add e₂ e₁)
  add-comm e₁ e₂ with eval e₁ | eval e₂
  ... | n | m = +-comm n m

  ac-prop : ∀ e₁ e₂ → Dec (eval (add e₁ e₂) ≡ eval (add e₂ e₁))
  ac-prop e₁ e₂ = eval (add e₁ e₂) ≟ eval (add e₂ e₁)
