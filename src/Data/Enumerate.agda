{-# OPTIONS --safe --without-K #-}

module Data.Enumerate where

open import Data.Nat
open import Data.Bool hiding (_≤_)
open import Data.Fin renaming (zero to fzero ; suc to fsuc) hiding (_+_ ; _≤_)

open import Data.List hiding (and)
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

  𝕗 : Set → Set
  𝕗 R = ℕ × R

  ffix : (𝕗 (R → R)) → R → R

  ffix (zero  , μ) z = z 
  ffix (suc n , μ) z = μ (ffix (n , μ) z) --n , μ (proj₂ (ffix (n , μ) z))

  REnum : Set → (I → Set) → Set 
  REnum {I = I} R P = ((i : I) → Enumerator (P i)) → Enumerator R

  IEnum : (I → Set) → Set
  IEnum {I} P = (i : I) → REnum (P i) P

  Enum : Set → Set
  Enum A = IEnum {⊤} λ where tt → A

  fix : IEnum {I} P → (i : I) → Enumerator (P i)
  fix e i n = ffix (n , flip e) (λ _ _ → []) i n

module _ where

  pure : R → REnum R P
  (pure x) _ _ = [ x ]

  ∅ : REnum R P
  ∅ _ _ = []

  infixl 10 _∥_

  _∥_ : REnum R P → REnum R P → REnum R P
  (xs ∥ ys) var n = xs var n ++ ys var n

  k  : Enumerator R → REnum R P
  k e _ n = e n
   
  _<*>_ : REnum (R₁ → R₂) P → REnum R₁ P → REnum R₂ P
  (fs <*> xs) μ n = concatMap (λ f → map f (xs μ n)) (fs μ n)

  var : (i : I) → REnum (P i) P
  (var i) μ = μ i

  ‼ : R → REnum R P
  ‼ x = pure x

  infixl 10 _⊛_
  _⊛_ = _<*>_

  infix 5 _⟨∣⟩_
  _⟨∣⟩_ = _∥_

  _>>=_ : REnum R₁ P → (R₁ → REnum R₂ P) → REnum R₂ P
  (f >>= g) μ n = concatMap (λ x → (g x) μ n) (f μ n)

module _ where 

  record Enumerable (R : Set) : Set where
    field 
      enumerator : Enum R

  open Enumerable public

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


  -- Predicates over recursive enumerators
  RPred : Set₁
  RPred = ∀ {I R P} → (e : REnum {I} R P) → (er : IEnum P) → Set

  Complete : RPred 
  Complete e er = ∀[ e (fix er) ↝_ ]

  Monotone : RPred
  Monotone e er = ∀ n m x →
                    e (fix er) ⟨ n ⟩↝ x →
                    n ≤ m →
                    e (fix er) ⟨ m ⟩↝ x

  IsComplete : Pred (IEnum P) 0ℓ
  IsComplete e = ∀[ (flip Complete) e ∘ e ]

  IsMonotone : Pred (IEnum P) 0ℓ
  IsMonotone e = ∀[ (flip Monotone) e ∘ e ]
