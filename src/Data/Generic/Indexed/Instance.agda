{-# OPTIONS --safe #-}

module Data.Generic.Indexed.Instance where 

open import Data.List
open import Data.Enumerate

open import Data.List.Membership.Propositional.Properties

open import Data.Generic.Indexed.Universe
open import Data.Generic.Indexed.Enumerator

open import Data.Generic.Indexed.Properties.Monotone
open import Data.Generic.Indexed.Properties.Complete

open import Function.Bundles
open import Function

open import Relation.Unary

module _ where 

  record HasIDesc {I} (P : I → Set) : Set₁ where 
    field
      func : Func Enumerator I
      P↔   : ∀ {i} → P i ↔ μ func i 

  open HasIDesc ⦃...⦄

  record IEnumerable {I} (P : I → Set) : Set where
    field
      #enum     : (i : I) → Enumerator (P i)

  open IEnumerable ⦃...⦄

  open Inverse

  instance
    genumerator : ⦃ _ : HasIDesc P ⦄ → IEnumerable P
    IEnumerable.#enum  genumerator i n = map (f⁻¹ P↔) (enum func i n)

  
