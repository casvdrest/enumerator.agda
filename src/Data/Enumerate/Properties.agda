{-# OPTIONS --safe #-}

module Data.Enumerate.Properties where

open import Data.List 
open import Data.Product
open import Data.Enumerate
open import Data.Generic.Indexed.Properties.Monotone
open import Data.List.Membership.Propositional.Properties

open import Function.Bundles
open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂ ; [_] to P[_])

module _ where 


-- Certified enumerators respect type isomorphisms
module _ where 

  open Inverse

  ap-iso : A ↔ B → Enumerator A → Enumerator B
  ap-iso iso e n = Data.List.map (f iso) (e n)

  mono-resp-↔ : ∀ {e} → (iso : A ↔ B) → Monotone e → Monotone (ap-iso iso e)
  mono-resp-↔ iso mn {x = y} elem lq
    with f⁻¹ iso y | inspect (f⁻¹ iso) y | proj₁ (inverse iso) y
  mono-resp-↔ iso mn {x = y} elem lq
    | x | P[ eq₁ ] | eq₂ rewrite eq₁ | sym eq₂ with mn {x = x} (elem-inv iso elem) lq
  ... | elem' = ∈-map⁺ (f iso) elem'

  comp-resp-↔ : ∀ {e} → (iso : A ↔ B) → Complete e → Complete (ap-iso iso e)
  loc (comp-resp-↔ iso cp {x}) = loc {x = f⁻¹ iso x} cp
  elem (comp-resp-↔ iso cp {x = y})
    with f⁻¹ iso y | inspect (f⁻¹ iso) y | proj₁ (inverse iso) y 
  ... | x | P[ eq₁ ] | eq₂ rewrite eq₁ | sym eq₂ = ∈-map⁺ (f iso) (elem cp)

  enum-resp-↔ : A ↔ B → CEnumerator A → CEnumerator B
  enum (enum-resp-↔ iso ce) = ap-iso iso (enum ce)
  mono (enum-resp-↔ iso ce) = mono-resp-↔ iso (mono ce)
  comp (enum-resp-↔ iso ce) = comp-resp-↔ iso (comp ce)

