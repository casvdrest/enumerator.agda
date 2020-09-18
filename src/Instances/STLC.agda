{-# OPTIONS --safe #-}

module Instances.STLC where

open import Data.Enumerate
open import Data.Enumerate.Properties

open import Data.Generic.Indexed.Universe
open import Data.Generic.Indexed.Enumerator
open import Data.Generic.Indexed.Properties.Monotone
open import Data.Generic.Indexed.Properties.Complete

open import Instances.Membership
open import Instances.Type

open import Data.List 
open import Data.Unit hiding (_≟_)
open import Data.Product
open import Data.Sum 
open import Data.Fin hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Empty

open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Properties

open import Function
open import Function.Bundles

open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂ ; [_] to P[_])
open import Relation.Nullary

-- Intrinsically-typed syntax for the simply-typed λ-calculus
module _ where  

  data Term : Ctx → Type → Set where
    tt    : Term Γ unit 
    ident : a ∈ Γ → Term Γ a
    abs   : Term (a ∷ Γ) b → Term Γ (a ⇒ b)
    app   : Term Γ (a ⇒ b) → Term Γ a → Term Γ b 

-- A generic description of the simply-typed λ-calculus
module _ where 

  unitD : IDesc CEnumerator (Ctx × Type)
  unitD = `1

  identD : Ctx → Type → IDesc CEnumerator (Ctx × Type)
  identD Γ a = `Σ (a ∈ Γ) {elems a Γ} λ _ → `1

  absD : Ctx → Type → Type → IDesc CEnumerator (Ctx × Type)
  absD Γ a b = `var (a ∷ Γ , b)

  appD : Ctx → Type → IDesc CEnumerator (Ctx × Type)
  appD Γ b = `Σ Type {types} λ a → `var (Γ , (a ⇒ b)) `× `var (Γ , a)


  TermF : Func CEnumerator (Ctx × Type)
  out TermF (Γ , t) = `σ 3 λ
    { zero             → identD Γ t
    ; (suc zero)       → appD Γ t
    ; (suc (suc zero)) →
         case t of λ
           { (a ⇒ b) → absD Γ a b
           ; unit    → unitD
           }
    }

-- TermF describes 'Term' (i.e., its fixpoint is isomorphic to 'Term')
module _ where 

  open Inverse

  TermF↔Term : ∀ {Γ a} → μ (mk (enums ∘ out TermF)) (Γ , a) ↔ Term Γ a
  
  f          TermF↔Term              ⟨ zero , a∈Γ , tt ⟩          = ident a∈Γ
  f          TermF↔Term              ⟨ suc zero , a , tm₁ , tm₂ ⟩ = app (f TermF↔Term tm₁) (f TermF↔Term tm₂)
  Inverse.f (TermF↔Term {a = a ⇒ b}) ⟨ suc (suc zero) , tm ⟩      = abs (f TermF↔Term tm)
  Inverse.f (TermF↔Term {a = unit }) ⟨ suc (suc zero) , tt ⟩      = tt

  f⁻¹ TermF↔Term tt            = ⟨ suc (suc zero) , tt ⟩
  f⁻¹ TermF↔Term (ident a∈Γ)   = ⟨ zero , a∈Γ , tt ⟩
  f⁻¹ TermF↔Term (abs tm)      = ⟨ suc (suc zero) , f⁻¹ TermF↔Term tm ⟩
  f⁻¹ TermF↔Term (app tm₁ tm₂) = ⟨ (suc zero , _ , (f⁻¹ TermF↔Term tm₁) , f⁻¹ TermF↔Term tm₂) ⟩
  
  cong₁ TermF↔Term refl = refl
  cong₂ TermF↔Term refl = refl

  proj₁ (inverse TermF↔Term)               tt = refl
  proj₁ (inverse (TermF↔Term {a = _ ⇒ _})) (ident x)     = refl
  proj₁ (inverse (TermF↔Term {a = unit })) (ident x)     = refl
  proj₁ (inverse TermF↔Term)               (abs tm)
    = cong abs (proj₁ (inverse TermF↔Term) tm)
  proj₁ (inverse (TermF↔Term {a = _ ⇒ _})) (app tm₁ tm₂)
    = pCong₂ app (proj₁ (inverse TermF↔Term) tm₁) (proj₁ (inverse TermF↔Term) tm₂)
  proj₁ (inverse (TermF↔Term {a = unit })) (app tm₁ tm₂)
    = pCong₂ app (proj₁ (inverse TermF↔Term) tm₁) (proj₁ (inverse TermF↔Term) tm₂)
  
  proj₂ (inverse (TermF↔Term {a = _ ⇒ _})) ⟨ zero , a∈Γ , tt ⟩          = refl
  proj₂ (inverse (TermF↔Term {a = unit })) ⟨ zero , a∈Γ , tt ⟩          = refl
  proj₂ (inverse (TermF↔Term {a = _ ⇒ _})) ⟨ suc zero , _ , tm₁ , tm₂ ⟩
    = pCong₂ (λ x y → ⟨ suc zero , _ , x , y ⟩) (proj₂ (inverse TermF↔Term) tm₁) (proj₂ (inverse TermF↔Term) tm₂)
  proj₂ (inverse (TermF↔Term {a = unit })) ⟨ suc zero , _ , tm₁ , tm₂ ⟩
    = pCong₂ (λ x y → ⟨ suc zero , _ , x , y ⟩) (proj₂ (inverse TermF↔Term) tm₁) (proj₂ (inverse TermF↔Term) tm₂)
  proj₂ (inverse (TermF↔Term {a = _ ⇒ _})) ⟨ suc (suc zero) , tm ⟩
    = cong (λ x → ⟨ suc (suc zero) , x ⟩) (proj₂ (inverse TermF↔Term) tm)
  proj₂ (inverse (TermF↔Term {a = unit })) ⟨ suc (suc zero) , tt ⟩      = refl


-- A certified enumerator for the simply-typed λ-calculus
module _ where

  open import Data.Generic.Indexed.CertifiedEnumerator

  terms : (Γ : Ctx) → (a : Type) → CEnumerator (Term Γ a) 
  terms Γ a = enum-resp-↔ TermF↔Term (cenumerate TermF (Γ , a))
