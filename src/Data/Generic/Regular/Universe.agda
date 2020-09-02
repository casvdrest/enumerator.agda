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

module _ where 

  enums : Desc CEnumerator → Desc Enumerator
  enums = enum ⟨$⟩_
