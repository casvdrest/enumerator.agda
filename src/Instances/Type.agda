{-# OPTIONS --safe #-}

module Instances.Type where

open import Data.Enumerate
open import Data.Enumerate.Properties

open import Data.Generic.Regular.Universe
open import Data.Generic.Regular.CertifiedEnumerator

open import Data.List 
open import Data.Unit hiding (_≟_)
open import Data.Product
open import Data.Sum 

open import Function.Bundles

open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂ ; [_] to P[_])
open import Relation.Nullary

module _ where

  data Type : Set where
    _⇒_  : (a b : Type) → Type
    unit : Type

-- A certified enumerator for list membership proofs
module _ where 

  _≟_ : (a b : Type) → Dec (a ≡ b)
  unit ≟ unit = yes refl
  (a₁ ⇒ b₁) ≟ (a₂ ⇒ b₂) with a₁ ≟ a₂ | b₁ ≟ b₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | yes refl | no ¬p    = no λ where refl → ¬p refl
  (_ ⇒ _) ≟ unit    = no λ()
  unit    ≟ (_ ⇒ _) = no λ()

  Ctx = List Type

  variable
    Γ : Ctx
    a b c : Type

  TypeD : Desc CEnumerator
  TypeD = (`var `× `var) `∪ `1

  open Inverse

  TypeD↔Type : μ (enums TypeD) ↔ Type
  f TypeD↔Type ⟨ inj₁ (a , b) ⟩ = f TypeD↔Type a ⇒ f TypeD↔Type b
  f TypeD↔Type ⟨ inj₂ tt ⟩ = unit
  f⁻¹ TypeD↔Type (a ⇒ b) = ⟨ (inj₁ (f⁻¹ TypeD↔Type a , f⁻¹ TypeD↔Type b)) ⟩
  f⁻¹ TypeD↔Type unit = ⟨ (inj₂ tt) ⟩
  cong₁ TypeD↔Type refl = refl
  cong₂ TypeD↔Type refl = refl
  proj₁ (inverse TypeD↔Type) (a ⇒ b)
    = pCong₂ _⇒_ (proj₁ (inverse TypeD↔Type) a) (proj₁ (inverse TypeD↔Type) b)
  proj₁ (inverse TypeD↔Type) unit = refl
  proj₂ (inverse TypeD↔Type) ⟨ inj₁ (a , b) ⟩
    = pCong₂ (λ a b → ⟨ (inj₁ (a , b)) ⟩) (proj₂ (inverse TypeD↔Type) a) (proj₂ (inverse TypeD↔Type) b)
  proj₂ (inverse TypeD↔Type) ⟨ inj₂ tt ⟩ = refl

  types : CEnumerator Type
  types = enum-resp-↔ TypeD↔Type (cenumerate TypeD)
