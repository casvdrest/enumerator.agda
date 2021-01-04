module Trie.EnumFold where 

open import Data.Nat
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.Sum 

open import Function

open import Level using (0ℓ ; Level ; Lift ; lift) renaming (zero to zeroL ; suc to sucL)

module _ where

  data Δ (R : Set) : Set where
    `0 `1 `var  : Δ R
    _`⊎_ _`×_   : (δ₁ δ₂ : R) → Δ R

  data Desc : Set where
    mk : Δ Desc → Desc

  ⟦_⟧ : Desc → Set → Set
  ⟦ mk `0         ⟧ X = ⊥
  ⟦ mk `1         ⟧ X = ⊤
  ⟦ mk `var       ⟧ X = X
  ⟦ mk (δ₁ `⊎ δ₂) ⟧ X = ⟦ δ₁ ⟧ X ⊎ ⟦ δ₂ ⟧ X
  ⟦ mk (δ₁ `× δ₂) ⟧ X = ⟦ δ₁ ⟧ X × ⟦ δ₂ ⟧ X

  data μ (δ : Desc) : Set where
    ⟨_⟩ : ⟦ δ ⟧ (μ δ) → μ δ

module _ where

  variable A B C : Set 

  mapᴰ : (A → B) → Δ A → Δ B
  mapᴰ f `0         = `0
  mapᴰ f `1         = `1
  mapᴰ f `var       = `var
  mapᴰ f (δ₁ `⊎ δ₂) = f δ₁ `⊎ f δ₂
  mapᴰ f (δ₁ `× δ₂) = f δ₂ `× f δ₂

module _ where

  open import Data.List

  variable d d' : Desc

  enumerate' :  → List (⟦ d ⟧ (μ d')) 
  enumerate' {d = mk `0} x = {!!}
  enumerate' {d = mk `1} x = {!!}
  enumerate' {d = mk `var} x = {!!}
  enumerate' {d = mk (δ₁ `⊎ δ₂)} x = {!!}
  enumerate' {d = mk (δ₁ `× δ₂)} x = {!!}
