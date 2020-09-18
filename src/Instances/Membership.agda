--{-# OPTIONS --safe #-}

module Instances.Membership where

open import Data.Enumerate
open import Data.Enumerate.Properties

open import Data.Generic.Indexed.Universe
open import Data.Generic.Indexed.Enumerator
open import Data.Generic.Indexed.Properties.Monotone
open import Data.Generic.Indexed.Properties.Complete
open import Data.Generic.Indexed.CertifiedEnumerator

open import Data.List 
open import Data.Unit hiding (_≟_)
open import Data.Product
open import Data.Sum 
open import Data.Fin hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Empty

open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Properties

open import Function
open import Function.Bundles

open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂ ; [_] to P[_])
open import Relation.Nullary
open import Relation.Unary hiding (_∈_ ; ∅)

module _ where 

  ∈F : ((x y : A) → Dec (x ≡ y)) →
       Func CEnumerator (A × List A)
  out (∈F _  ) (x , [])     = `σ 0 λ()
  out (∈F _≟_) (x , y ∷ xs) with x ≟ y
  ... | yes refl = `σ 2 λ { zero       → `1
                          ; (suc zero) → `var (x , xs) }
  ... | no ×≠y   = `var (x , xs)
  
  open Inverse
  
  postulate ∈F↔∈ : ∀ {x xs} → (dec : (x y : A) → Dec (x ≡ y)) → μ (mk (enums ∘ (out $ ∈F dec))) (x , xs) ↔ x ∈ xs

  elems : ∀ Γ a → (dec : (x y : A) → Dec (x ≡ y)) → CEnumerator (a ∈ Γ)
  elems Γ a dec = enum-resp-↔ (∈F↔∈ dec) (cenumerate (∈F dec) (a , Γ))

 {-
  _≟_ : (a b : Type) → Dec (a ≡ b)
  unit ≟ unit = yes refl
  (a₁ ↦ b₁) ≟ (a₂ ↦ b₂) with a₁ ≟ a₂ | b₁ ≟ b₂
  ... | [yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | yes refl | no ¬p    = no λ where refl → ¬p refl
  (_ ↦ _) ≟ unit    = no λ()
  unit    ≟ (_ ↦ _) = no λ()
  -
  elems : ∀ Γ a → Enumerator (a ∈ Γ)
  elems [] a = ∅
  elems (b ∷ Γ) a with a ≟ b
  ... | yes refl = ‼ (here refl) ⟨∣⟩ (‼ there ⊛ elems Γ a)
  ... | no  ¬p   = ‼ there ⊛ elems Γ a

  there-inv₁ : ∀ {a} {Γ : Ctx} {xs : List (a ∈ Γ)} {px : a ∈ Γ} →
                 there px ∈ [ here refl ] ++ concatMap (λ f → Data.List.map f xs) [ there ] →
                 px ∈ xs 
  there-inv₁ {a} {Γ} {xs} (there elem)
    with ∈-map⁻ there (∈-resp-≡ (++-identityʳ _) elem)
  ... | _ , elem' , refl = elem'

  there-inv₂ : ∀ {a} {b} {Γ : Ctx} {xs : List (a ∈ Γ)} {px : a ∈ Γ} →
               there {x = b} px ∈ concatMap (λ f → Data.List.map f xs) [ there ] →
               px ∈ xs
  there-inv₂ elem with ∈-map⁻ there (∈-resp-≡ (++-identityʳ _) elem)
  ... | _ , elem' , refl = elem'

  elems-monotone : ∀ Γ a → Monotone (elems Γ a)
  elems-monotone (b ∷ Γ) .b {x = here refl} elem lq
    with b ≟ b
  ... | yes refl = here refl
  ... | no ¬p    = ⊥-elim (¬p refl)
  elems-monotone (b ∷ Γ) a {x = there x} elem lq
    with a ≟ b 
  ... | yes refl = ∈-++⁺ʳ [ here refl ] (∈-++⁺ˡ (∈-map⁺ there (elems-monotone Γ b (there-inv₁ elem) lq)))
  ... | no _     = ∈-++⁺ˡ (∈-map⁺ there (elems-monotone Γ a (there-inv₂ elem) lq))

  elems-complete : ∀ Γ a → Complete (elems Γ a) 
  elems-complete (b ∷ Γ) .b {here refl}
    with b ≟ b
  ... | yes refl = ↑l 0 (here refl)
  ... | no  ¬p   = ⊥-elim (¬p refl)
  elems-complete (b ∷ Γ) a {there px}
    with a ≟ b | elems-complete Γ a {px}
  ... | yes refl | ↑l loc elem' = ↑l loc (∈-++⁺ʳ [ here refl ] (∈-++⁺ˡ (∈-map⁺ there elem')))
  ... | no _     | ↑l loc elem' = ↑l loc (∈-++⁺ˡ (∈-map⁺ there elem'))

-}
