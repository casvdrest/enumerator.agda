module Data.Generic.Regular.Universe where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Enumerate

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

  map-reg : ∀ d → (X → Y) → ⟦ d ⟧ X → ⟦ d ⟧ Y
  map-reg (d₁ `∪ d₂) f (inj₁ x) = inj₁ (map-reg d₁ f x)
  map-reg (d₁ `∪ d₂) f (inj₂ y) = inj₂ (map-reg d₂ f y)
  map-reg (d₁ `× d₂) f (x , y)  = (map-reg d₁ f x) , (map-reg d₂ f y)
  map-reg `var       f x        = f x
  map-reg `1         f tt       = tt
  map-reg (`k S)     f x        = x

module _ where 

  record IsRegular (R : Set) : Set₁ where
    field
      desc : Desc (Σ Set Enum)
      iso  : R ↔ μ (proj₁ ⟨$⟩ desc)

module _ where 

  record k-info (S : Set) : Set₁ where
    field
      E : Enum S
      k-monotone : Monotone (E tt) E
      k-complete : Complete (E tt) E

  open k-info public 

  enums : Σ Set k-info → Σ Set Enum
  enums (S , ki) = S , E ki
