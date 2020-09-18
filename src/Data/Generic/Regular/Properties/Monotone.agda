{-# OPTIONS --safe #-}

module Data.Generic.Regular.Properties.Monotone where

open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Enumerate
open import Data.List
open import Data.Empty

open import Data.Generic.Regular.Universe
open import Data.Generic.Regular.Enumerator

open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there)

open import Relation.Binary.PropositionalEquality using (refl ; cong ; cong₂ ; _≡_ ; sym ; trans)

-- open import Function using (_$_ ; const)
open import Function.Bundles

module _ where 

  -- membership respects propositional equality
  ∈-resp-≡ : ∀ {A : Set} {x : A} {xs ys} → xs ≡ ys → x ∈ xs → x ∈ ys
  ∈-resp-≡ refl el = el

  -- ⟨_⟩ is bijective
  open Inverse renaming (cong₂ to Icong₂)

  μ-iso : ∀ {d : Desc F} → ⟦ d ⟧ (μ d) ↔ μ d
  f   μ-iso x = ⟨ x ⟩ 
  f⁻¹ μ-iso ⟨ x ⟩ = x

  cong₁ μ-iso refl = refl
  Icong₂ μ-iso refl = refl
  
  proj₁ (inverse μ-iso) ⟨ x ⟩     = refl
  proj₂ (inverse μ-iso) _  = refl


  -- If f x is an element of f mapped over xs, and f is bijective, then x is
  -- must be an element of xs. 
  --------------------------------------------------------------------------------------

  elem-inv : ∀ (inj : R₁ ↔ R₂) {x xs} →
                f inj x ∈ map (f inj) xs → 
                x ∈ xs
  elem-inv inj {xs = x ∷ xs} (here px) = here (trans (sym (proj₂ (inverse inj) _))
                                           (trans (cong (f⁻¹ inj) px)
                                                  (proj₂ (inverse inj) _))
                                                  )
  elem-inv inj {xs = x ∷ xs} (there px) = there (elem-inv inj px)


  -- Some helper lemmas for coproduct enumerators
  --------------------------------------------------------------------------------------

  map-inj₁-inv : ∀ {A B : Set} {x : A} {xs} → inj₁ {B = B} x ∈ Data.List.map inj₁ xs → x ∈ xs
  map-inj₁-inv {xs = x₁ ∷ xs} (here refl) = here refl
  map-inj₁-inv {xs = x₁ ∷ xs} (there el) = there (map-inj₁-inv el)

  map-inj₂-inv : ∀ {A B : Set} {y : B} {ys} → inj₂ {A = A} y ∈ Data.List.map inj₂ ys → y ∈ ys
  map-inj₂-inv {ys = y ∷ ys} (here refl) = here refl
  map-inj₂-inv {ys = y ∷ ys} (there el) = there (map-inj₂-inv el)

  inj₁≠inj₂ : ∀ {A B : Set} {x : A} {ys : List B} → inj₁ x ∈ Data.List.map inj₂ ys → ⊥
  inj₁≠inj₂ {ys = x ∷ ys} (there el) = inj₁≠inj₂ el

  inj₂≠inj₁ : ∀ {A B : Set} {y : B} {xs : List A} → inj₂ y ∈ Data.List.map inj₁ xs → ⊥ 
  inj₂≠inj₁ {xs = x ∷ xs} (there el) = inj₂≠inj₁ el

  inj₁-inv : ∀ {A B : Set} {n} (e₁ : Enumerator A) (e₂ : Enumerator B) {x : A} →
               inj₁ x ∈ map inj₁ (e₁ n) ++ map inj₂ (e₂ n) → x ∈ e₁ n
  inj₁-inv e₁ e₂ el with ∈-++⁻ (map inj₁ (e₁ _)) el
  ... | inj₁ x = map-inj₁-inv x
  ... | inj₂ y = ⊥-elim (inj₁≠inj₂ y)

  inj₂-inv : ∀ {A B : Set} {n} (e₁ : Enumerator A) (e₂ : Enumerator B) {y : B} →
               inj₂ y ∈ map inj₁ (e₁ n) ++ map inj₂ (e₂ n) → y ∈ e₂ n
  inj₂-inv e₁ e₂ el with ∈-++⁻ (map inj₁ (e₁ _)) el
  ... | inj₁ x = ⊥-elim (inj₂≠inj₁ x)
  ... | inj₂ y = map-inj₂-inv y


  -- Product equivalence, allows us to reuse lemmas from stdlib for cartesian product of
  -- lists. 
  --------------------------------------------------------------------------------------

  product-equiv : ∀ {A B : Set} {xs : List A} {ys : List B} →
                    concatMap (λ f → map f ys) (concatMap (λ f → map f xs) [ _,_ ]) ≡
                    cartesianProduct xs ys
  product-equiv {xs = []} {ys} = refl
  product-equiv {xs = x ∷ xs}  = cong (λ xs → map (x ,_) _ ++ xs) (product-equiv {xs = xs})


  -- Monotonicity theorem for the generic enumerator for regular types
  --------------------------------------------------------------------------------------

  monotone' : ∀ {d' : Desc CEnumerator} {d : Desc CEnumerator} → Monotone (enumerate' {enums d'} (enums d))

  monotone' {d = d₁ `∪ d₂} {x = inj₁ x} el lq
    = ∈-++⁺ˡ ( ∈-map⁺ inj₁ (monotone' {d = d₁}
                 (inj₁-inv (enumerate' (enums d₁)) (enumerate' (enums d₂)) el) lq))
  monotone' {d = d₁ `∪ d₂} {x = inj₂ y} el lq
    = ∈-++⁺ʳ _ ( ∈-map⁺ inj₂ (monotone' {d = d₂}
                   (inj₂-inv (enumerate' (enums  d₁)) (enumerate' (enums d₂)) el) lq))

  monotone' {d = d₁ `× d₂} {x = x , y} el lq
    = ∈-resp-≡ (sym (product-equiv {xs = enumerate' (enums d₁) _}))
               (∈-cartesianProduct⁺
                 (monotone' {d = d₁} (proj₁ (∈-cartesianProduct⁻ (enumerate' (enums d₁) _) (enumerate' (enums d₂) _)
                   (∈-resp-≡ (product-equiv {xs = enumerate' (enums d₁) _}) el))) lq)
                 (monotone' {d = d₂} (proj₂ (∈-cartesianProduct⁻ (enumerate' (enums d₁) _) (enumerate' (enums d₂) _)
                   (∈-resp-≡ (product-equiv {xs = enumerate' (enums d₁) _}) el))) lq))
                   
  monotone' {d'} {d = `var} {suc n} {x = ⟨ x ⟩} el (s≤s lq)
    with monotone' {d = d'} {x = x} (elem-inv μ-iso el) lq
  ... | r = ∈-map⁺ ⟨_⟩ r
  
  monotone' {d = `1} (here refl) lq = here refl

  monotone' {d = `k S {ki}} el lq = mono ki el lq

  monotone : (D : Desc CEnumerator) → Monotone (enumerate (enums D))
  monotone D {x = ⟨ x ⟩} el lq
    with monotone' {D} {D} {x = x}
                   (elem-inv μ-iso (∈-resp-≡ (++-identityʳ _) el)) lq
  ... | r = ∈-++⁺ˡ (∈-map⁺ ⟨_⟩ r)
