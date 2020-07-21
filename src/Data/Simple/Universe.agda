{-# OPTIONS --safe --without-K #-}

module Data.Simple.Universe where

open import Data.Unit
open import Data.Sum

module _ where 

  data U : Set where
    `1   : U
    `var : U
    _`+_   : U → U → U 

  ⟦_⟧ : U → Set → Set
  ⟦ `1       ⟧ X = ⊤
  ⟦ `var     ⟧ X = X
  ⟦ u₁ `+ u₂ ⟧ X = ⟦ u₁ ⟧ X ⊎ ⟦ u₂ ⟧ X

  data μ (u : U) : Set where
    ⟨_⟩ : ⟦ u ⟧ (μ u) → μ u

  

  
  
