{-# OPTIONS --safe #-}

module Instances.Membership where

open import Instances.Type

open import Data.Enumerate
open import Data.Generic.Indexed.Properties.Monotone

open import Data.List 
open import Data.Product
open import Data.Empty

open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Properties

open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂ ; [_] to P[_])
open import Relation.Nullary

module _ where 
  
  enum-elems : ∀ Γ a → Enumerator (a ∈ Γ)
  enum-elems [] a = ∅
  enum-elems (b ∷ Γ) a with a ≟ b
  ... | yes refl = ‼ (here refl) ⟨∣⟩ (‼ there ⊛ enum-elems Γ a)
  ... | no  ¬p   = ‼ there ⊛ enum-elems Γ a

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

  elems-monotone : ∀ Γ a → Monotone (enum-elems Γ a)
  elems-monotone (b ∷ Γ) .b {x = here refl} elem lq
    with b ≟ b
  ... | yes refl = here refl
  ... | no ¬p    = ⊥-elim (¬p refl)
  elems-monotone (b ∷ Γ) a {x = there x} elem lq
    with a ≟ b 
  ... | yes refl = ∈-++⁺ʳ [ here refl ] (∈-++⁺ˡ (∈-map⁺ there (elems-monotone Γ b (there-inv₁ elem) lq)))
  ... | no _     = ∈-++⁺ˡ (∈-map⁺ there (elems-monotone Γ a (there-inv₂ elem) lq))

  elems-complete : ∀ Γ a → Complete (enum-elems Γ a) 
  elems-complete (b ∷ Γ) .b {here refl}
    with b ≟ b
  ... | yes refl = ↑l 0 (here refl)
  ... | no  ¬p   = ⊥-elim (¬p refl)
  elems-complete (b ∷ Γ) a {there px}
    with a ≟ b | elems-complete Γ a {px}
  ... | yes refl | ↑l loc elem' = ↑l loc (∈-++⁺ʳ [ here refl ] (∈-++⁺ˡ (∈-map⁺ there elem')))
  ... | no _     | ↑l loc elem' = ↑l loc (∈-++⁺ˡ (∈-map⁺ there elem'))

  elems : ∀ a Γ → CEnumerator (a ∈ Γ)
  enum (elems a Γ) = enum-elems Γ a
  mono (elems a Γ) = elems-monotone Γ a
  comp (elems a Γ) = elems-complete Γ a
