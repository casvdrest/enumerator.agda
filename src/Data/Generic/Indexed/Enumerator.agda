{-# OPTIONS --safe #-}

module Data.Generic.Indexed.Enumerator where

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit 
open import Data.Enumerate
open import Data.List
open import Data.Nat
open import Data.Fin

open import Data.Generic.Indexed.Universe

open import Relation.Binary.PropositionalEquality using (refl ; cong ; _≡_)

open import Function using (const ; Inverse ; id ; _$_)

module _ where 

  enumerateFin : ∀ n → Enumerator (Fin n)
  enumerateFin zero = ∅
  enumerateFin (suc n) = ‼ zero ⟨∣⟩ (‼ suc ⊛ enumerateFin n)

  enumerate : ∀ {φ : Func Enumerator I} (d : IDesc Enumerator I) → Enumerator (⟦ d ⟧ (μ φ))
  enumerate          (d₁ `× d₂)  n       = concatMap (λ f → map f (enumerate d₂ n)) (concatMap (λ f → map f (enumerate d₁ n)) [ _,_ ])
  enumerate         `1                   = ‼ tt
  enumerate {φ = φ} (`var i)     zero    = []
  enumerate {φ = φ} (`var i)     (suc n) = map ⟨_⟩ (enumerate (out φ i) n)
  enumerate         (`σ m f)     n       = concatMap (λ fn → map (fn ,_) (enumerate (f fn) n)) (enumerateFin m n)
  enumerate         (`Σ S {e} f) n       = concatMap (λ s → map (s ,_) (enumerate (f s) n)) (e n)

  enum : (φ : Func Enumerator I) → (i : I) → Enumerator (μ φ i)
  enum φ i = ‼ ⟨_⟩ ⊛ enumerate (out φ i)

  