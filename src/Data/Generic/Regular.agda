module Data.Generic.Regular where

open import Data.Unit using (⊤ ; tt)
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.List

open import Data.Enumerate

open import Relation.Unary hiding (∅ ; _∈_)

open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; sym)
open import Function
open import Function.Bundles

module _ where 

  infix 10 _`∪_ _`×_
  -- Universe definition
  data Desc (K : Set₁) : Set₁ where
    _`∪_ _`×_  : (d₁ d₂ : Desc K) → Desc K
    `var `1 `0 : Desc K
    `k         : K → Desc K 

  variable
    K₁ K₂ : Set₁

  infix 15 _⟨$⟩_
  _⟨$⟩_ : (K₁ → K₂) → Desc K₁ → Desc K₂
  f ⟨$⟩ (d₁ `∪ d₂) = f ⟨$⟩ d₁ `∪ f ⟨$⟩ d₂
  f ⟨$⟩ (d₁ `× d₂) = f ⟨$⟩ d₁ `× f ⟨$⟩ d₂
  f ⟨$⟩ `var       = `var
  f ⟨$⟩ `1         = `1
  f ⟨$⟩ `0         = `0
  f ⟨$⟩ `k x       = `k (f x)

  ⟦_⟧ : Desc Set → (Set → Set)
  ⟦ d₁ `∪ d₂ ⟧ X = ⟦ d₁ ⟧ X ⊎ ⟦ d₂ ⟧ X
  ⟦ d₁ `× d₂ ⟧ X = ⟦ d₁ ⟧ X × ⟦ d₂ ⟧ X
  ⟦ `var     ⟧ X = X
  ⟦ `1       ⟧ X = ⊤
  ⟦ `0       ⟧ X = ⊥
  ⟦ `k S     ⟧ X = S

  data μ (d : Desc Set) : Set where
    ⟨_⟩ : ⟦ d ⟧ (μ d) → μ d

  variable
    X Y : Set
    d d' : Desc Set
    n m : ℕ

  map-reg : ∀ d → (X → Y) → ⟦ d ⟧ X → ⟦ d ⟧ Y
  map-reg (d₁ `∪ d₂) f (inj₁ x) = inj₁ (map-reg d₁ f x)
  map-reg (d₁ `∪ d₂) f (inj₂ y) = inj₂ (map-reg d₂ f y)
  map-reg (d₁ `× d₂) f (x , y)  = (map-reg d₁ f x) , (map-reg d₂ f y)
  map-reg `var       f x        = f x
  map-reg `1         f tt       = tt
  map-reg (`k S)     f x        = x

  record IsRegular (R : Set) : Set₁ where
    field
      desc : Desc Set
      iso  : R ↔ μ desc


  
  enumerate : (d : Desc (Σ Set Enum)) →
             REnum {⊤} (⟦ proj₁ ⟨$⟩ d ⟧ (μ d')) (const (μ d'))
  
  enumerate (d₁ `∪ d₂)   =  ‼ inj₁ ⊛ enumerate d₁ ⟨∣⟩
                            ‼ inj₂ ⊛ enumerate d₂
  enumerate (d₁ `× d₂)   = ‼ _,_ ⊛ enumerate d₁
                                 ⊛ enumerate d₂
  enumerate `var         = var tt
  enumerate `1           = ‼ tt
  enumerate `0           = ∅
  enumerate (`k (S , e)) = k e tt


  enumerate-μ : (d : Desc (Σ Set Enum)) → Enum (μ (proj₁ ⟨$⟩ d))
  enumerate-μ d tt = ‼ ⟨_⟩ ⊛ enumerate d


  
