{-# OPTIONS --safe --without-K #-}

module Data.Generic.Indexed.Universe where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Enumerate

open import Data.Nat
open import Data.Fin

open import Function
open import Function.Bundles

open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional

open import Relation.Unary

module _ where

  infix 10 _`×_
  -- Universe definition
  data IDesc (F : Set → Set) (I : Set) : Set₁ where
    _`×_ : (d₁ d₂ : IDesc F I) → IDesc F I
    `1 : IDesc F I
    `var : (i : I) → IDesc F I
    `σ : (n : ℕ) → (Fin n → IDesc F I) → IDesc F I  
    `Σ : (S : Set) → {F S} → (S → IDesc F I) → IDesc F I

  ⟦_⟧ : ∀ {F} → IDesc F I → (I → Set) → Set
  ⟦ d₁ `× d₂ ⟧ X = ⟦ d₁ ⟧ X × ⟦ d₂ ⟧ X
  ⟦ `1       ⟧ X = ⊤
  ⟦ `var i   ⟧ X = X i
  ⟦ `σ n f   ⟧ X = Σ (Fin n) λ fn → ⟦ f fn ⟧ X
  ⟦ `Σ S f   ⟧ X = Σ S       λ s  → ⟦ f s  ⟧ X

  variable
    F F₁ F₂ : Set → Set

  _⟨$⟩_ : ∀[ F₁ ⇒ F₂ ] → IDesc F₁ I → IDesc F₂ I
  f ⟨$⟩ (d₁ `× d₂) = (f ⟨$⟩ d₁) `× (f ⟨$⟩ d₂)
  f ⟨$⟩ `1 = `1
  f ⟨$⟩ `var i = `var i
  f ⟨$⟩ `σ n f' = `σ n (f ⟨$⟩_ ∘ f')
  f ⟨$⟩ `Σ S {si} f' = `Σ S {f si} (f ⟨$⟩_ ∘ f')

  record Func (F : Set → Set) (I : Set) : Set₁ where
    constructor mk
    field       out : I → IDesc F I 

  open Func public

  data μ {F I} (φ : Func F I) (i : I) : Set where
    ⟨_⟩ : ⟦ out φ i ⟧ (μ φ) → μ φ i

  module _ where

  enums : IDesc CEnumerator I → IDesc Enumerator I 
  enums = enum ⟨$⟩_
