{-# OPTIONS --safe #-}

module Data.Generic.Regular.Enumerator where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Enumerate
open import Data.List

open import Data.Generic.Regular.Universe

open import Relation.Binary.PropositionalEquality using (refl ; cong)

open import Function using (const ; Inverse ; id ; _$_)

module _ where 
  
  enumerate : {d' : Desc Enum} (d : Desc Enum) → REnum (         ⟦ d  ⟧ (μ d'))
                                                       ( const $ ⟦ d' ⟧ (μ d'))
  enumerate (d₁ `∪ d₂)
    = ‼ inj₁ ⊛ enumerate d₁ ⟨∣⟩
      ‼ inj₂ ⊛ enumerate d₂
  enumerate (d₁ `× d₂)
    = ‼ _,_ ⊛ enumerate d₁
            ⊛ enumerate d₂
  enumerate `var = ‼ ⟨_⟩ ⊛ var tt
  enumerate `1 = ‼ tt
  enumerate `0 = ∅
  enumerate (`k S {e}) = k (e tt (fix e))

  enumerate-μ : {d' : Desc Enum} (d : Desc Enum) → Enum (μ d)
  enumerate-μ d tt _ n = Data.List.map ⟨_⟩ (enumerate d (fix (const $ enumerate d)) n)

  open IsRegular ⦃...⦄
  open Inverse

  -- instance reg-enumerable : ⦃ _ : IsRegular R ⦄ → Enumerable R
  -- enumerator reg-enumerable n = ‼ (f⁻¹ iso) ⊛ k (enumerate-μ desc) tt

  -- open Enumerable 

  -- -- instance pair-regular : ⦃ _ : IsRegular A ⦄ ⦃ _ : IsRegular B ⦄ → IsRegular (A × B)
  -- -- IsRegular.desc (pair-regular {A} {B})
  -- --   = `k (A , enumerator reg-enumerable) `× `k (B , (enumerator reg-enumerable))
  
  -- -- f (IsRegular.iso pair-regular) (x , y) = ⟨ x , y ⟩
  -- -- f⁻¹ (IsRegular.iso pair-regular) ⟨ x , y ⟩ = x , y
  
  -- -- cong₁ (IsRegular.iso pair-regular) refl = refl
  -- -- cong₂ (IsRegular.iso pair-regular) refl = refl
  
  -- -- proj₁ (inverse (IsRegular.iso pair-regular)) ⟨ _ ⟩ = refl
  -- -- proj₂ (inverse (IsRegular.iso pair-regular)) _     = refl


  -- -- open import Data.Nat

  -- -- instance nat-regular : IsRegular ℕ
  -- -- IsRegular.desc nat-regular = `1 `∪ `var
  
  -- -- f (IsRegular.iso nat-regular) zero    = ⟨ inj₁ tt ⟩
  -- -- f (IsRegular.iso nat-regular) (suc n) = ⟨ (inj₂ (f iso n)) ⟩
  
  -- -- f⁻¹ (IsRegular.iso nat-regular) ⟨ inj₁ tt ⟩ = zero
  -- -- f⁻¹ (IsRegular.iso nat-regular) ⟨ inj₂ n ⟩  = suc (f⁻¹ iso n)

  -- -- cong₁ (IsRegular.iso nat-regular) refl = refl
  -- -- cong₂ (IsRegular.iso nat-regular) refl = refl

  -- -- proj₁ (inverse (IsRegular.iso nat-regular)) ⟨ inj₁ tt ⟩ = refl
  -- -- proj₁ (inverse (IsRegular.iso nat-regular)) ⟨ inj₂ n ⟩  = cong (λ n → ⟨ (inj₂ n) ⟩)  (proj₁ (inverse iso) n)
  -- -- proj₂ (inverse (IsRegular.iso nat-regular)) zero    = refl
  -- -- proj₂ (inverse (IsRegular.iso nat-regular)) (suc n) = cong suc (proj₂ (inverse iso) n)

  -- -- nats : Enum ℕ
  -- -- nats = enumerator reg-enumerable

  -- -- open import Relation.Binary.PropositionalEquality

  -- -- test : fix nats tt 10 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  -- -- test = refl

  -- -- nats' : Enum ℕ
  -- -- nats' tt = ‼ zero ⟨∣⟩ ‼ suc ⊛ var tt

  -- -- test' : fix nats' tt 10 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  -- -- test' = refl

  -- -- nats'' : Enum (μ (`1 `∪ `var))
  -- -- nats'' = enumerate-μ (`1 `∪ `var)

  -- -- lst = fix nats'' tt 10

  -- -- test'' : lst ≡ ⟨ inj₁ tt ⟩ -- 0 
  -- --              ∷ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ -- 1
  -- --              ∷ ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩ -- 2 
  -- --              ∷ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩ ⟩ -- 3
  -- --              ∷ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩ ⟩ ⟩ -- 4
  -- --              ∷ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ -- 5
  -- --              ∷ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ -- 6
  -- --              ∷ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ -- 7 
  -- --              ∷ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ -- 8 
  -- --              ∷ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ -- 9  
  -- --              ∷ []
  -- -- test'' = refl

  -- -- _ : length (fix (λ where tt → ‼ id ⊛ k nats'' tt) tt 10) ≡ 10
  -- -- _ = refl
