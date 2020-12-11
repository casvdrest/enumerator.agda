module Enumerate where


open import Data.Empty
open import Data.Unit
open import Data.Sum using (inj₁ ; inj₂ ; _⊎_)
open import Data.Product using (_,_ ; _×_)
open import Data.Nat

open import Data.List
open import Data.List.Categorical

open import Category.Functor
open import Category.Applicative
open import Category.Monad

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


  open RawFunctor ⦃...⦄
  open RawApplicative ⦃...⦄
  open RawMonad ⦃...⦄

  instance list-monad = monad

  enumerate' : ∀ d {d'} → (n : ℕ) → List (⟦ d ⟧ (μ d')) 
  enumerate' `0   _       = []
  enumerate' `1   _       = [ tt ]
  enumerate' `var zero    = []
  enumerate' `var (suc n) = map ⟨_⟩ (enumerate' _ n)
  enumerate' (d₁ `⊎ d₂) n = map inj₁ (enumerate' d₁ n) ++ map inj₂ (enumerate' d₂ n)
  enumerate' (d₁ `× d₂) n = do
    x ← enumerate' d₁ n
    y ← enumerate' d₂ n
    return (x , y)

  enumerate : ∀ d (n : ℕ) → List (μ d)
  enumerate d n = map ⟨_⟩ (enumerate' d n) 
