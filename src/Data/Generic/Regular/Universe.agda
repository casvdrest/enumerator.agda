{-# OPTIONS --safe #-}

module Data.Generic.Regular.Universe where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Enumerate

open import Function.Bundles

open import Relation.Unary

module _ where 

  infix 10 _`∪_ _`×_
  -- Universe definition
  data Desc (F : Set → Set) : Set₁ where
    _`∪_ _`×_  : (d₁ d₂ : Desc F) → Desc F
    `var `1 `0 : Desc F
    `k         : (S : Set) → {F S} → Desc F 

  variable
    F F₁ F₂ : Set → Set

  infix 15 _⟨$⟩_
  _⟨$⟩_ : ∀[ F₁ ⇒ F₂ ] → Desc F₁ → Desc F₂
  f ⟨$⟩ (d₁ `∪ d₂) = f ⟨$⟩ d₁ `∪ f ⟨$⟩ d₂
  f ⟨$⟩ (d₁ `× d₂) = f ⟨$⟩ d₁ `× f ⟨$⟩ d₂
  f ⟨$⟩ `var       = `var
  f ⟨$⟩ `1         = `1
  f ⟨$⟩ `0         = `0
  f ⟨$⟩ `k s {p}   = `k s {f p}

  ⟦_⟧ : Desc F → (Set → Set)
  ⟦ d₁ `∪ d₂ ⟧ X = ⟦ d₁ ⟧ X ⊎ ⟦ d₂ ⟧ X
  ⟦ d₁ `× d₂ ⟧ X = ⟦ d₁ ⟧ X × ⟦ d₂ ⟧ X
  ⟦ `var     ⟧ X = X
  ⟦ `1       ⟧ X = ⊤
  ⟦ `0       ⟧ X = ⊥
  ⟦ `k S     ⟧ X = S

  data μ (d : Desc F) : Set where
    ⟨_⟩ : ⟦ d ⟧ (μ d) → μ d

  variable
    X Y : Set
    d d' : Desc F

  map-reg : ∀ (d : Desc F) → (X → Y) → ⟦ d ⟧ X → ⟦ d ⟧ Y
  map-reg (d₁ `∪ d₂) f (inj₁ x) = inj₁ (map-reg d₁ f x)
  map-reg (d₁ `∪ d₂) f (inj₂ y) = inj₂ (map-reg d₂ f y)
  map-reg (d₁ `× d₂) f (x , y)  = (map-reg d₁ f x) , (map-reg d₂ f y)
  map-reg `var       f x        = f x
  map-reg `1         f tt       = tt
  map-reg (`k S)     f x        = x

module _ where 

  record IsRegular (R : Set) : Set₁ where
    field
      desc : Desc Enum
      iso  : R ↔ μ desc

module _ where 

  record k-info (S : Set) : Set where
    field
      E : Enum S
      k-monotone : Monotone (E tt) E
      k-complete : IsComplete E

  open k-info public 

  enums : Desc k-info → Desc Enum
  enums = E ⟨$⟩_
