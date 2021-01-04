{-# OPTIONS --without-K #-}

module Trie.Trie where

open import Relation.Binary.PropositionalEquality hiding ([_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function

variable A B C : Set

postulate fun-ext : (f g : A → B) → (∀ x → f x ≡ g x) → (f ≡ g)

module _ where

  record HasTrie (A : Set) : Set₁ where 
     field A-↛_    : (B : Set) → Set  
           trie    : (A → B) → (A-↛ B)
           untrie  : (A-↛ B) → (A → B)

           inverseₗ : trie ∘ untrie ≡ id {A = A-↛ B} 
           inverseᵣ : untrie ∘ trie ≡ id {A = A → B}

  open HasTrie ⦃...⦄ public

  
  _↛_ : (A B : Set) → ⦃ HasTrie A ⦄ → Set 
  A ↛ B = A-↛ B

  memo : ⦃ HasTrie A ⦄ → (A → B) → (A → B)
  memo = untrie ∘ trie

  -- Memoization is a safe program transformation
  memo-safe : (f : A → B) → ⦃ _ : HasTrie A ⦄ → ∀ x → memo f x ≡ f x
  memo-safe f x = cong-app (cong-app inverseᵣ f) x

module _ where

  open import Data.Unit

  instance ⊤-hastrie : HasTrie ⊤
  HasTrie.A-↛_     ⊤-hastrie B = ⊤ → B
  HasTrie.trie     ⊤-hastrie f tt = f tt
  HasTrie.untrie   ⊤-hastrie f tt = f tt
  HasTrie.inverseₗ ⊤-hastrie = refl
  HasTrie.inverseᵣ ⊤-hastrie = refl


module _ where

  open import Data.Empty

  instance ⊥-hastrie : HasTrie ⊥
  (HasTrie.A-↛     ⊥-hastrie) B = ⊥ → B
  HasTrie.trie     ⊥-hastrie x = x
  HasTrie.untrie   ⊥-hastrie _ ()
  HasTrie.inverseₗ ⊥-hastrie = fun-ext _ _ λ _ → fun-ext _ _ λ()
  HasTrie.inverseᵣ ⊥-hastrie = fun-ext _ _ λ _ → fun-ext _ _ λ()

module _ where

  open import Data.Sum
  open import Data.Product

  instance ⊎-hastrie : ⦃ HasTrie A ⦄ → ⦃ HasTrie B ⦄ → HasTrie (A ⊎ B)
  (HasTrie.A-↛     ⊎-hastrie {A} {B}) C = (A ↛ C) × (B ↛ C)
  HasTrie.trie     ⊎-hastrie f = trie (f ∘ inj₁) , trie (f ∘ inj₂)
  HasTrie.untrie   ⊎-hastrie (f , g) = [ untrie f , untrie g ]
  HasTrie.inverseₗ ⊎-hastrie = fun-ext _ _ λ (f , g) → cong₂ _,_ (cong-app inverseₗ f) (cong-app inverseₗ g)
  HasTrie.inverseᵣ ⊎-hastrie = fun-ext _ _ λ f → fun-ext _ f [ (λ x → cong (_$ x) (cong-app inverseᵣ (f ∘ inj₁)))
                                                             , (λ y → cong (_$ y) (cong-app inverseᵣ (f ∘ inj₂))) ]


-- Inverse proofs taken from https://github.com/conal/MemoTrie/blob/master/src/Data/MemoTrie.hs
module _ where

  open import Data.Product
  
  instance ×-hastrie : ⦃ p₁ : HasTrie A ⦄ → ⦃ p₂ : HasTrie B ⦄ → HasTrie (A × B)
  (HasTrie.A-↛ ×-hastrie {A} {B}) C = A ↛ (B ↛ C)
  HasTrie.trie ×-hastrie f = trie (trie ∘ curry f)
  HasTrie.untrie ×-hastrie f = uncurry (untrie ∘ untrie f)
  HasTrie.inverseₗ (×-hastrie {A} {B} ⦃ p₁ ⦄ ⦃ p₂ ⦄) =
    let trie₁   = trie   ⦃ p₁ ⦄ ; trie₂   = trie   ⦃ p₂ ⦄ ; trie×   = trie   ⦃ ×-hastrie {A} {B} ⦄ in
    let untrie₁ = untrie ⦃ p₁ ⦄ ; untrie₂ = untrie ⦃ p₂ ⦄ ; untrie× = untrie ⦃ ×-hastrie {A} {B} ⦄ in
    fun-ext _ _ λ t → begin
    trie× (untrie× t)
      ≡⟨⟩
    trie× (uncurry (untrie₂ ∘ untrie₁ t))
      ≡⟨⟩
    trie₁ (trie₂ ∘ curry (uncurry (untrie₂ ∘ untrie₁ t)))
      ≡⟨⟩
    trie₁ (trie₂ ∘ untrie₂ ∘ untrie₁ t)
      ≡⟨ cong trie₁ (cong (λ f x → f $ untrie₁ t x) (inverseₗ ⦃ p₂ ⦄)) ⟩
    trie₁ (untrie₁ t)
      ≡⟨ cong-app (inverseₗ ⦃ p₁ ⦄) t ⟩
    t ∎
  HasTrie.inverseᵣ (×-hastrie {A} {B} ⦃ p₁ ⦄ ⦃ p₂ ⦄) = fun-ext _ _ λ f → begin
    untrie (trie f)
      ≡⟨⟩
    untrie (trie (trie ∘ curry f))
      ≡⟨⟩
    uncurry (untrie ∘ untrie (trie (trie ∘ curry f)))
      ≡⟨ cong uncurry (cong (λ f' x y → untrie (f' (trie ∘ curry f) x) y) inverseᵣ) ⟩
    uncurry (untrie ∘ trie ∘ curry f)
      ≡⟨ cong (λ f' → uncurry (f' ∘ curry f)) inverseᵣ ⟩
    uncurry (curry f)
      ≡⟨⟩
    f ∎
