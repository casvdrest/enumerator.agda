{-# OPTIONS --safe #-}

module Data.Generic.Regular.Enumerator where

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit 
open import Data.Enumerate
open import Data.List
open import Data.Nat

open import Data.Generic.Regular.Universe

open import Relation.Binary.PropositionalEquality using (refl ; cong ; _≡_)

open import Function using (const ; Inverse ; id ; _$_)

module _ where 

  enumerate : {d' : Desc Enumerator} → (d : Desc Enumerator) → Enumerator (⟦ d ⟧ (μ d'))
  enumerate      (d₁ `∪ d₂) n       = map inj₁ (enumerate d₁ n) ++ map inj₂ (enumerate d₂ n)
  enumerate      (d₁ `× d₂) n       = concatMap (λ f → map f (enumerate d₂ n)) (concatMap (λ f → map f (enumerate d₁ n)) [ _,_ ])
  enumerate      `var       zero    = []
  enumerate {d'} `var       (suc n) = map ⟨_⟩ (enumerate d' n)
  enumerate `1                      = ‼ tt
  enumerate `0                      = ∅
  enumerate (`k _ {e})              = e

  enum : (d : Desc Enumerator) → Enumerator (μ d)
  enum d = ‼ ⟨_⟩ ⊛ enumerate d
