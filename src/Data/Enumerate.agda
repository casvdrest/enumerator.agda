{-# OPTIONS --safe --without-K #-}

module Data.Enumerate where

open import Data.Nat
open import Data.Bool hiding (_≤_)
open import Data.Fin renaming (zero to fzero ; suc to fsuc) hiding (_+_ ; _≤_)

open import Data.List hiding (and )
open import Data.List.Membership.Propositional

open import Data.Unit hiding (_≤_)
open import Data.Product hiding (map)

open import Relation.Unary hiding (∅ ; _∈_)

open import Category.Applicative

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

module _ where

  variable
    A B C I R R₁ R₂ : Set
    P Q : I → Set 

  Enumerator : Set → Set
  Enumerator A = (n : ℕ) → List A

module _ where

  ∅ : Enumerator R 
  ∅ n = []

  infixl 10 _⟨∣⟩_
  
  _⟨∣⟩_ : Enumerator R → Enumerator R → Enumerator R
  (xs ⟨∣⟩ ys) n = xs n ++ ys n

  ‼ : R → Enumerator R
  ‼ x n = [ x ]

  infixl 10 _⊛_
  _<*>_ : Enumerator (R₁ → R₂) → Enumerator R₁ → Enumerator R₂
  (fs <*> xs) n = concatMap ((flip map) (xs n)) (fs n)

  _>>=_ : Enumerator R₁ → (R₁ → Enumerator R₂) → Enumerator R₂
  (f >>= g) n = concatMap (flip g n) (f n)

  _⊛_ = _<*>_

module _ where

  open import Level

  _⟨_⟩↝_ : (e : Enumerator R) → (n : ℕ) → (x : R) → Set
  e ⟨ n ⟩↝ x = x ∈ e n

  
  -- Enumerator production. 'e ↝ r' means that 'e' will eventually produce 'r' at some depth 
  record _↝_ (e : Enumerator R) (x : R) : Set where
    constructor ↑l 
    field 
      loc  : ℕ
      elem : e ⟨ loc ⟩↝ x

  open _↝_ public

  Complete : Enumerator R → Set
  Complete e = ∀[ e ↝_ ]

  Monotone : Enumerator R → Set
  Monotone e = ∀ {n m} → ∀[ e ⟨ n ⟩↝_ ⇒ (λ _ → n ≤ m) ⇒ e ⟨ m ⟩↝_ ]

  record CEnumerator (S : Set) : Set where
    field
      enum : Enumerator S
      mono : Monotone enum 
      comp : Complete enum

  open CEnumerator public
