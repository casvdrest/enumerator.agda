{-# OPTIONS --safe #-}

module Instances.STLC where

open import Data.Enumerate
open import Data.Generic.Indexed.Universe
open import Data.Generic.Indexed.Enumerator
open import Data.Generic.Indexed.Instance

open import Data.List
open import Data.Unit 
open import Data.Product
open import Data.Sum
open import Data.Fin
open import Data.Nat
open import Data.Bool
open import Data.Empty

open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any

open import Function
open import Function.Bundles

open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂)
open import Relation.Nullary
open import Relation.Unary hiding (_∈_)

module _ where 

  data Type : Set where
    _↦_  : (s t : Type) → Type
    unit : Type
  
  Ctx = List Type

  data Term : Ctx × Type → Set where
  
    var : ∀ {Γ t}
          → t ∈ Γ
            ------------
          → Term (Γ , t)
    
    abs : ∀ {Γ s t}
          → Term (s ∷ Γ , t)
            ----------------
          → Term (Γ , s ↦ t)
          
    app : ∀ {Γ s t}
          → Term (Γ , s ↦ t)
          → Term (Γ , s)
            ------------
          → Term (Γ , t)

    unit : ∀ {Γ}
             ---------------
           → Term (Γ , unit)


module _ where 

  TypeF : Func Enumerator ⊤
  out TypeF tt = `σ 2 λ
    { zero       → `var tt `× `var tt
    ; (suc zero) → `1
    }

  open Inverse

  Type→ : ∀[ const Type ⇒ μ TypeF ]
  Type→ (t₁ ↦ t₂) = ⟨ (zero , Type→ t₁ , Type→ t₂) ⟩
  Type→ unit      = ⟨ (suc zero , tt) ⟩

  Type← : ∀[ μ TypeF ⇒ const Type ]
  Type← ⟨ zero , t₁ , t₂ ⟩ = Type← t₁ ↦ Type← t₂
  Type← ⟨ suc zero  , tt ⟩ = unit

  Type↔ : ∀ {i} → const Type i ↔ μ TypeF i

  f       Type↔ = Type→ 
  f⁻¹     Type↔ = Type←

  cong₁ Type↔ refl = refl
  cong₂ Type↔ refl = refl
  
  proj₁ (inverse Type↔) ⟨ zero , t₁ , t₂ ⟩
    = pCong₂ (λ x y → ⟨ zero , x , y ⟩) (proj₁ (inverse Type↔) t₁) (proj₁ (inverse Type↔) t₂)
  proj₁ (inverse Type↔) ⟨ suc zero , snd ⟩ = refl

  proj₂ (inverse Type↔) (t₁ ↦ t₂)
    = pCong₂ _↦_ (proj₂ (inverse Type↔) t₁) (proj₂ (inverse Type↔) t₂)
  proj₂ (inverse Type↔) unit = refl

  instance
    type-idesc : HasIDesc (const Type)
    HasIDesc.func type-idesc = TypeF
    HasIDesc.P↔ type-idesc = Type↔

  


  
