{-# OPTIONS --safe --without-K #-}

module Data.Generic.Indexed.Enumerator where

open import Data.Product hiding (map)
open import Data.Unit 
open import Data.Enumerate
open import Data.List
open import Data.Nat
open import Data.Fin

open import Data.Generic.Indexed.Universe

module _ where 

  fins : ∀ n → Enumerator (Fin n)
  fins zero    = ∅
  fins (suc n) = ‼ zero ⟨∣⟩ (‼ suc ⊛ fins n)

  enumerate' : ∀ {φ : Func Enumerator I} (d : IDesc Enumerator I) → Enumerator (⟦ d ⟧ (μ φ))
  enumerate'          (d₁ `× d₂)  n       = concatMap (λ f → map f (enumerate' d₂ n)) (concatMap (λ f → map f (enumerate' d₁ n)) [ _,_ ])
  enumerate'         `1                   = ‼ tt
  enumerate' {φ = φ} (`var i)     zero    = []
  enumerate' {φ = φ} (`var i)     (suc n) = map ⟨_⟩ (enumerate' (out φ i) n)
  enumerate'         (`σ m f)     n       = concatMap (λ fn → map (fn ,_) (enumerate' (f fn) n)) (fins m n)
  enumerate'         (`Σ S {e} f) n       = concatMap (λ s → map (s ,_) (enumerate' (f s) n)) (e n)

  enumerate : (φ : Func Enumerator I) → (i : I) → Enumerator (μ φ i)
  enumerate φ i n = map ⟨_⟩ (enumerate' (out φ i) n)
