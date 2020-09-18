{-# OPTIONS --safe #-}

module Data.Generic.Regular.Properties.Complete where

open import Data.Enumerate
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Nat

open import Data.Generic.Regular.Universe
open import Data.Generic.Regular.Enumerator
open import Data.Generic.Regular.Properties.Monotone

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; inspect ; cong₂ ; trans)

open import Function using (const ; id ; _$_)

module _ where

  max : ℕ → ℕ → ℕ
  max zero    m       = m
  max (suc n) zero    = suc n
  max (suc n) (suc m) = suc (max n m)

  ≤-refl : ∀ n → n ≤ n
  ≤-refl zero    = z≤n
  ≤-refl (suc n) = s≤s (≤-refl n)

  n≤maxnm : ∀ n m → n ≤ max n m
  n≤maxnm zero    m       = z≤n
  n≤maxnm (suc n) zero    = ≤-refl _
  n≤maxnm (suc n) (suc m) = s≤s (n≤maxnm n m)

  m≤maxnm : ∀ n m → m ≤ max n m
  m≤maxnm zero    m       = ≤-refl _
  m≤maxnm (suc n) zero    = z≤n
  m≤maxnm (suc n) (suc m) = s≤s (m≤maxnm n m)


  -- Completeness theorem for the generic enumerator for regular types. 
  --------------------------------------------------------------------------------------

  complete' : ∀ {d'} (d : Desc CEnumerator) → Complete (enumerate' {d' = enums d'} (enums d)) 

  loc  (complete' (d₁ `∪ d₂) {inj₁ x}) = loc (complete' d₁ {x})
  elem (complete' (d₁ `∪ d₂) {inj₁ x}) = ∈-++⁺ˡ (∈-map⁺ inj₁ (elem (complete' d₁ {x})))
  
  loc  (complete' (d₁ `∪ d₂) {inj₂ y}) = loc (complete' d₂ {y})
  elem (complete' (d₁ `∪ d₂) {inj₂ y}) = ∈-++⁺ʳ _ (∈-map⁺ inj₂ (elem (complete' d₂ {y})))

  loc  (complete' (d₁ `× d₂) {x , y}) = max (loc (complete' d₁ {x})) (loc (complete' d₂ {y}))
  elem (complete' {d'} (d₁ `× d₂) {x , y}) =
    ∈-resp-≡ (sym $ product-equiv {xs = enumerate' (enums d₁) _})
      ( ∈-cartesianProduct⁺
          ( monotone' {d = d₁} (elem (complete' d₁ {x})) (n≤maxnm _ _))
          ( monotone' {d = d₂} (elem (complete' d₂ {y})) (m≤maxnm _ _))
      )

  loc  (complete' {d'} `var {⟨ x ⟩}) = suc (loc (complete' d' {x}))
  elem (complete' {d'} `var {⟨ x ⟩}) = ∈-map⁺ ⟨_⟩ (elem (complete' d' {x}))

  loc  (complete' `1) = 0
  elem (complete' `1) = here refl
  
  complete' (`k S {cert}) = comp cert

  complete : (D : Desc CEnumerator) → Complete (enumerate (enums D))
  loc (complete D {⟨ x ⟩}) = loc {x = x} (complete' {D} D)
  elem (complete D {⟨ x ⟩}) = ∈-++⁺ˡ (∈-map⁺ ⟨_⟩ (elem (complete' D)))
