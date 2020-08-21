{-# OPTIONS --safe #-}

module Data.Generic.Indexed.Properties.Complete where

open import Data.List
open import Data.Enumerate
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Fin hiding (_≤_)

open import Data.Generic.Indexed.Universe
open import Data.Generic.Indexed.Enumerator
open import Data.Generic.Indexed.Properties.Monotone

open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there)

open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; inspect ; cong₂ ; trans)

open import Function.Bundles
open import Function using (const ; id ; _$_)

open import Function

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

  ef-complete : ∀ {n} → Complete (enumerateFin n) 

  loc  (ef-complete {suc n} {zero})  = 0
  elem (ef-complete {suc n} {zero}) = here refl

  loc  (ef-complete {suc n} {suc x}) = loc {x = x} (ef-complete {n})
  elem (ef-complete {suc n} {suc x}) =
    ∈-++⁺ʳ [ zero ] (∈-resp-≡ (sym $ ++-identityʳ _) (∈-map⁺ suc (elem (ef-complete {n}))))


  complete : ∀ {φ : Func Σ-info I} (d : IDesc Σ-info I) → Complete (enumerate {φ = mk (enums ∘ out φ)} (enums d))

  loc  (complete (d₁ `× d₂)) = max (loc (complete d₁)) (loc (complete d₂))
  elem (complete (d₁ `× d₂) {x , y}) = ∈-resp-≡ (sym $ product-equiv {xs = enumerate (enums d₁) _})
      ( ∈-cartesianProduct⁺
          ( monotone {d = d₁} (elem (complete d₁ {x})) (n≤maxnm _ _))
          ( monotone {d = d₂} (elem (complete d₂ {y})) (m≤maxnm _ _))
      )

  loc  (complete `1) = 0
  elem (complete `1) = here refl

  loc  (complete {φ = φ} (`var i) {⟨ _ ⟩}) = suc (loc (complete (out φ i)))
  elem (complete {φ = φ} (`var i) {⟨ _ ⟩}) = ∈-map⁺ (⟨_⟩) (elem (complete (out φ i)))

  loc  (complete (`σ n f) {fn , x}) = max (loc {x = fn} (ef-complete {n})) (loc (complete (f fn) {x}))
  elem (complete (`σ n f) {fn , x}) =
    ∈-Σ⁺ (ef-monotone (elem (ef-complete {n})) (n≤maxnm (loc {x = fn} ef-complete) (loc (complete (f fn) {x}))))
         (monotone {d = f fn} (elem (complete (f fn))) (m≤maxnm (loc {x = fn} ef-complete) _))

  loc  (complete (`Σ S {si} f) {s , x}) = max (loc {x = s} (Σ-complete si)) (loc (complete (f s) {x}))
  elem (complete (`Σ S {si} f) {s , x}) =
    ∈-Σ⁺ (Σ-monotone si (elem (Σ-complete si)) (n≤maxnm _ _))
         (monotone {d = f s} (elem (complete (f s) {x})) (m≤maxnm _ _))
