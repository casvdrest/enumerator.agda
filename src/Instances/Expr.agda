{-# OPTIONS --safe #-}

module Instances.Expr where

open import Data.Nat hiding (_≤_)
open import Data.Nat.Properties
open import Data.Bool hiding (_≤_) renaming (_≟_ to _≟b_)
open import Data.Fin using (suc ; zero ; Fin)
open import Data.Product
open import Data.Sum
open import Data.Unit using (tt)

open import Data.Enumerate
open import Data.Enumerate.Properties

open import Data.Generic.Indexed.Universe renaming (μ to μᴵ ; enums to enumsᴵ)
open import Data.Generic.Indexed.CertifiedEnumerator renaming (cenumerate to cenumerateᴵ)

open import Data.Generic.Regular.Universe 
open import Data.Generic.Regular.CertifiedEnumerator 

open import Function
open import Function.Bundles

module _ where

  data Type : Set where
    𝕟 𝕓 : Type

  data Expr : Type → Set where 
    add  : Expr 𝕟 → Expr 𝕟 → Expr 𝕟
    and  : Expr 𝕓 → Expr 𝕓 → Expr 𝕓
    leq  : Expr 𝕟 → Expr 𝕟 → Expr 𝕓
    bool : Bool → Expr 𝕓
    nat  : ℕ → Expr 𝕟

  Value : Type → Set
  Value 𝕟 = ℕ
  Value 𝕓 = Bool

  variable
    t : Type

  _≤_ : ℕ → ℕ → Bool 
  zero  ≤ m     = true
  suc n ≤ zero  = false
  suc n ≤ suc m = n ≤ m

  eval : Expr t → Value t
  eval (add e₁ e₂) = eval e₁ + eval e₂
  eval (and e₁ e₂) = eval e₁ ∨ eval e₂
  eval (leq e₁ e₂) = eval e₁ ≤ eval e₂
  eval (bool b)    = b
  eval (nat n)     = n


module _ where

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  add-comm : ∀ e₁ e₂ → eval (add e₁ e₂) ≡ eval (add e₂ e₁)
  add-comm e₁ e₂ with eval e₁ | eval e₂
  ... | n | m = +-comm n m

  ac-prop : ∀ e₁ e₂ → Dec (eval (add e₁ e₂) ≡ eval (add e₂ e₁))
  ac-prop e₁ e₂ = eval (add e₁ e₂) ≟ eval (add e₂ e₁)


module _ where

  NatD : Desc CEnumerator
  NatD = `1 `∪ `var

  open Inverse
  open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂)

  NatD↔Nat : μ (enums NatD) ↔ ℕ

  f NatD↔Nat ⟨ inj₁ tt ⟩ = zero
  f NatD↔Nat ⟨ inj₂ n ⟩ = suc (f NatD↔Nat n)

  f⁻¹ NatD↔Nat zero = ⟨ inj₁ tt ⟩
  f⁻¹ NatD↔Nat (suc n) = ⟨ inj₂ (f⁻¹ NatD↔Nat n) ⟩

  cong₁ NatD↔Nat refl = refl
  cong₂ NatD↔Nat refl = refl
  
  proj₁ (inverse NatD↔Nat) zero = refl
  proj₁ (inverse NatD↔Nat) (suc n) = cong suc (proj₁ (inverse NatD↔Nat) n)

  proj₂ (inverse NatD↔Nat) ⟨ inj₁ tt ⟩ = refl
  proj₂ (inverse NatD↔Nat) ⟨ inj₂ n ⟩ = cong (λ n → ⟨ inj₂ n ⟩) (proj₂ (inverse NatD↔Nat) n)

  nats : CEnumerator ℕ
  nats = enum-resp-↔ NatD↔Nat (cenumerate NatD) 

module _ where

  BoolD : Desc CEnumerator
  BoolD = `1 `∪ `1

  open Inverse
  open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂)

  BoolD↔Bool : μ (enums BoolD) ↔ Bool
  f BoolD↔Bool ⟨ inj₁ tt ⟩ = false
  f BoolD↔Bool ⟨ inj₂ tt ⟩ = true
  
  f⁻¹ BoolD↔Bool false = ⟨ (inj₁ tt) ⟩
  f⁻¹ BoolD↔Bool true  = ⟨ (inj₂ tt) ⟩
  
  cong₁ BoolD↔Bool refl = refl
  cong₂ BoolD↔Bool refl = refl

  proj₁ (inverse BoolD↔Bool) false = refl
  proj₁ (inverse BoolD↔Bool) true = refl

  proj₂ (inverse BoolD↔Bool) ⟨ inj₁ tt ⟩ = refl
  proj₂ (inverse BoolD↔Bool) ⟨ inj₂ tt ⟩ = refl

  bools : CEnumerator Bool
  bools = enum-resp-↔ BoolD↔Bool (cenumerate BoolD)

module _ where

  ExprF : Func CEnumerator Type
  out ExprF 𝕟 = `σ 2 λ
    { zero              → `var 𝕟 `× `var 𝕟
    ; (suc zero)        → `Σ ℕ {nats} λ _ → `1
    }
  out ExprF 𝕓 = `σ 3 λ
    { zero             → `var 𝕓 `× `var 𝕓
    ; (suc zero)       → `var 𝕟 `× `var 𝕟
    ; (suc (suc zero)) → `Σ Bool {bools} λ _ → `1
    }

  open Inverse
  open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂)

  ExprF↔Expr : μᴵ (mk (enumsᴵ ∘ out ExprF)) t ↔ Expr t
  f (ExprF↔Expr {𝕟}) ⟨ zero , e₁ , e₂ ⟩ = add (f ExprF↔Expr e₁) (f ExprF↔Expr e₂)
  f (ExprF↔Expr {𝕟}) ⟨ suc zero , n , tt ⟩ = nat n
  f (ExprF↔Expr {𝕓}) ⟨ zero , e₁ , e₂ ⟩ = and (f ExprF↔Expr e₁) (f ExprF↔Expr e₂)
  f (ExprF↔Expr {𝕓}) ⟨ suc zero , e₁ , e₂ ⟩ = leq (f ExprF↔Expr e₁) (f ExprF↔Expr e₂)
  f (ExprF↔Expr {𝕓}) ⟨ suc (suc zero) , b , tt ⟩ = bool b
  
  f⁻¹ ExprF↔Expr (add e₁ e₂) = ⟨ (zero , f⁻¹ ExprF↔Expr e₁ , f⁻¹ ExprF↔Expr e₂) ⟩
  f⁻¹ ExprF↔Expr (and e₁ e₂) = ⟨ (zero , (f⁻¹ ExprF↔Expr e₁) , (f⁻¹ ExprF↔Expr e₂)) ⟩
  f⁻¹ ExprF↔Expr (leq e₁ e₂) = ⟨ (suc zero , f⁻¹ ExprF↔Expr e₁ , f⁻¹ ExprF↔Expr e₂) ⟩
  f⁻¹ ExprF↔Expr (bool b) = ⟨ ((suc (suc zero)) , b , tt) ⟩
  f⁻¹ ExprF↔Expr (nat n) = ⟨ (suc zero , n , tt) ⟩
  
  cong₁ ExprF↔Expr refl = refl
  cong₂ ExprF↔Expr refl = refl
  
  proj₁ (inverse ExprF↔Expr) (add e₁ e₂) = pCong₂ add (proj₁ (inverse ExprF↔Expr) e₁) (proj₁ (inverse ExprF↔Expr) e₂)
  proj₁ (inverse ExprF↔Expr) (and e₁ e₂) = pCong₂ and (proj₁ (inverse ExprF↔Expr) e₁) (proj₁ (inverse ExprF↔Expr) e₂)
  proj₁ (inverse ExprF↔Expr) (leq e₁ e₂) = pCong₂ leq (proj₁ (inverse ExprF↔Expr) e₁) (proj₁ (inverse ExprF↔Expr) e₂)
  proj₁ (inverse ExprF↔Expr) (bool x) = refl
  proj₁ (inverse ExprF↔Expr) (nat x)  = refl
  
  proj₂ (inverse (ExprF↔Expr {𝕟})) ⟨ zero , e₁ , e₂ ⟩ = pCong₂ (λ x y → ⟨ zero , x , y ⟩) (proj₂ (inverse ExprF↔Expr) e₁) (proj₂ (inverse ExprF↔Expr) e₂)
  proj₂ (inverse (ExprF↔Expr {𝕟})) ⟨ suc zero , n , tt ⟩ = refl
  proj₂ (inverse (ExprF↔Expr {𝕓})) ⟨ zero , e₁ , e₂ ⟩ = pCong₂ (λ x y → ⟨ zero , x , y ⟩) (proj₂ (inverse ExprF↔Expr) e₁) (proj₂ (inverse ExprF↔Expr) e₂)
  proj₂ (inverse (ExprF↔Expr {𝕓})) ⟨ suc zero , e₁ , e₂ ⟩ = pCong₂ (λ x y → ⟨ suc zero , x , y ⟩) (proj₂ (inverse ExprF↔Expr) e₁) (proj₂ (inverse ExprF↔Expr) e₂)
  proj₂ (inverse (ExprF↔Expr {𝕓})) ⟨ suc (suc zero) , b , tt ⟩ = refl

  exprs : (t : Type) → CEnumerator (Expr t)
  exprs t = enum-resp-↔ ExprF↔Expr (cenumerateᴵ ExprF t)


