module Data.Generic.Instances where

open import Data.Generic.Regular
open import Data.Enumerate

open import Function.Bundles
open import Function

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.List

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

module _ where 

  open IsRegular  ⦃...⦄
  open Enumerable ⦃...⦄
  open Inverse

  instance reg-enumerable : ⦃ _ : IsRegular R ⦄ → Enumerable R
  enumerator reg-enumerable = enumerate (const (‼ (f⁻¹ iso) ⊛ k (enum-reg-μ desc) tt)) tt

  instance nat-regular : IsRegular ℕ
  IsRegular.desc nat-regular = `1 `⊎ `var
  
  f     (IsRegular.iso nat-regular) zero    = ⟨ inj₁ tt ⟩
  f     (IsRegular.iso nat-regular) (suc n) = ⟨ inj₂ (f iso n) ⟩
  
  f⁻¹ (IsRegular.iso nat-regular) ⟨ inj₁ tt ⟩ = zero
  f⁻¹ (IsRegular.iso nat-regular) ⟨ inj₂ n ⟩  = suc (f⁻¹ iso n)

  cong₁ (IsRegular.iso nat-regular) refl = refl

  cong₂ (IsRegular.iso nat-regular) refl = refl

  proj₁ (inverse (IsRegular.iso nat-regular)) ⟨ inj₁ x ⟩ = refl
  proj₁ (inverse (IsRegular.iso nat-regular)) ⟨ inj₂ n ⟩ = cong (λ n → ⟨ inj₂ n ⟩) (proj₁ (inverse iso) n)
  
  proj₂ (inverse (IsRegular.iso nat-regular)) zero    = refl
  proj₂ (inverse (IsRegular.iso nat-regular)) (suc n) = cong suc (proj₂ (inverse iso) n)


  nats′ : Enumerator ℕ
  nats′ = Enumerable.enumerator reg-enumerable

  test : nats′ 10 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] 
  test = refl
