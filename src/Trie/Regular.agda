module Trie.Regular where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Trie.Trie

open import Function
import Function.Construct.Symmetry as S

open import Relation.Binary.PropositionalEquality hiding ([_])
open Relation.Binary.PropositionalEquality.≡-Reasoning


module _ where

  data Desc : Set₁ where
    `0 `1 `var : Desc
    _`⊎_ _`×_ : (d₁ d₂ : Desc) → Desc

  ⟦_⟧ : Desc → (Set → Set)
  ⟦ `0        ⟧ X = ⊥
  ⟦ `1        ⟧ X = ⊤
  ⟦ `var      ⟧ X = X
  ⟦ d₁ `⊎ d₂  ⟧ X = ⟦ d₁ ⟧ X ⊎ ⟦ d₂ ⟧ X
  ⟦ d₁ `× d₂  ⟧ X = ⟦ d₁ ⟧ X × ⟦ d₂ ⟧ X

  data μ (d : Desc) : Set where
    ⟨_⟩ : ⟦ d ⟧ (μ d) → μ d

  variable d d₁ d₂ : Desc
  
  μ-iso : ⟦ d ⟧ (μ d) ↔ μ d
  Inverse.f   μ-iso   x   = ⟨ x ⟩
  Inverse.f⁻¹ μ-iso ⟨ x ⟩ = x
  Inverse.cong₁ μ-iso refl = refl
  Inverse.cong₂ μ-iso refl = refl
  proj₁ (Inverse.inverse μ-iso) ⟨ x ⟩ = refl
  proj₂ (Inverse.inverse μ-iso) x     = refl

  mapᴿ : ∀ d → (A → B) → ⟦ d ⟧ A → ⟦ d ⟧ B 
  mapᴿ `0         f = id
  mapᴿ `1         f = id
  mapᴿ `var       f = f
  mapᴿ (d₁ `⊎ d₂) f = [ inj₁ ∘ mapᴿ d₁ f , inj₂ ∘ mapᴿ d₂ f ]
  mapᴿ (d₁ `× d₂) f = < mapᴿ d₁ f ∘ proj₁ , mapᴿ d₂ f ∘ proj₂ >

  record Regular (A : Set) : Set₁ where
    field desc  : Desc
          iso   : A ↔ μ desc

  open Regular ⦃...⦄
  open HasTrie
  open Inverse

  trie-iso : HasTrie A → A ↔ B → HasTrie B
  A-↛       trie-iso t eqv  = A-↛ t
  trie     (trie-iso t eqv) = trie t ∘ _∘ f eqv
  untrie   (trie-iso t eqv) = (_∘ f⁻¹ eqv) ∘ untrie t
  inverseₗ (trie-iso t eqv) = fun-ext _ _ λ x → begin
   trie t (untrie t x ∘ f⁻¹ eqv ∘ f eqv)
     ≡⟨ cong (trie t) (fun-ext _ _ λ y → cong (untrie t x) (proj₂ (inverse eqv) _)) ⟩
   trie t (untrie t x)
     ≡⟨ cong-app (inverseₗ t) x ⟩
    x ∎
  inverseᵣ (trie-iso t eqv) = fun-ext _ _ λ g → fun-ext _ _ λ x →
    begin untrie t (trie t (g ∘ f eqv)) (f⁻¹ eqv x)
      ≡⟨ cong-app (cong-app (inverseᵣ t) (g ∘ f eqv)) (f⁻¹ eqv x) ⟩
    g (f eqv (f⁻¹ eqv x))
      ≡⟨ cong g (proj₁ (inverse eqv) x) ⟩ 
    g x ∎

  {-# TERMINATING #-}
  desc-trie' : ∀ d₁ d → HasTrie (⟦ d₁ ⟧ (μ d))
  desc-trie' `0 d = ⊥-hastrie
  desc-trie' `1 d = ⊤-hastrie
  desc-trie' `var d = trie-iso (desc-trie' d d) μ-iso
  desc-trie' (d₁ `⊎ d₂) d = ⊎-hastrie ⦃ desc-trie' d₁ _ ⦄ ⦃ desc-trie' d₂ _ ⦄
  desc-trie' (d₁ `× d₂) d = ×-hastrie ⦃ desc-trie' d₁ _ ⦄ ⦃ desc-trie' d₂ _ ⦄

  desc-trie : HasTrie (μ d)
  desc-trie {d} = trie-iso (desc-trie' d d) μ-iso

  instance regular-hastree : ⦃ Regular A ⦄ → HasTrie A
  regular-hastree = trie-iso desc-trie (S.sym-↔ iso)

module _ where

  open import Data.Nat

  natD : Desc
  natD = `1 `⊎ `var

  instance nat-regular : Regular ℕ
  Regular.desc nat-regular = natD
  Inverse.f (Regular.iso nat-regular) zero = ⟨ inj₁ tt ⟩
  Inverse.f (Regular.iso nat-regular) (suc n) = ⟨ inj₂ (Inverse.f (Regular.iso nat-regular) n) ⟩
  Inverse.f⁻¹ (Regular.iso nat-regular) ⟨ inj₁ tt ⟩ = zero
  Inverse.f⁻¹ (Regular.iso nat-regular) ⟨ inj₂ n ⟩ = suc (Inverse.f⁻¹ (Regular.iso nat-regular) n)
  Inverse.cong₁ (Regular.iso nat-regular) refl = refl
  Inverse.cong₂ (Regular.iso nat-regular) refl = refl
  proj₁ (Inverse.inverse (Regular.iso nat-regular)) ⟨ inj₁ tt ⟩ = refl
  proj₁ (Inverse.inverse (Regular.iso nat-regular)) ⟨ inj₂ y ⟩ = cong (λ x → ⟨ inj₂ x ⟩) (proj₁ (Inverse.inverse (Regular.iso nat-regular)) y)
  proj₂ (Inverse.inverse (Regular.iso nat-regular)) zero = refl
  proj₂ (Inverse.inverse (Regular.iso nat-regular)) (suc n) = cong suc (proj₂ (Inverse.inverse (Regular.iso nat-regular)) n)

  fib : (n : ℕ) → ℕ
  fib zero = 1
  fib (suc zero) = 1
  fib (suc (suc n)) = fib n + fib (suc n)

  fib_m : (n : ℕ) → ℕ
  fib_m = memo fib
