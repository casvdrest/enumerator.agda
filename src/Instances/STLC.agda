{-# OPTIONS --safe #-}

module Instances.STLC where

open import Data.Enumerate
open import Data.Generic.Indexed.Universe
open import Data.Generic.Indexed.Enumerator
open import Data.Generic.Indexed.Properties.Monotone
open import Data.Generic.Indexed.Properties.Complete


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

open import Function
open import Function.Bundles

open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂) hiding ([_])
open import Relation.Nullary
open import Relation.Unary hiding (_∈_ ; ∅)

module _ where 

  data Type : Set where
    _↦_  : (a b : Type) → Type
    unit : Type
  
  Ctx = List Type

  variable
    Γ : Ctx
    a b c d : Type 

  data Term : Ctx → Type → Set where
    tt    : Term Γ unit 
    ident : a ∈ Γ → Term Γ a
    abs   : Term (a ∷ Γ) b → Term Γ (a ↦ b)
    app   : Term Γ (a ↦ b) → Term Γ a → Term Γ b 

module _ where 

  _≟_ : (a b : Type) → Dec (a ≡ b)
  unit ≟ unit = yes refl
  (a₁ ↦ b₁) ≟ (a₂ ↦ b₂) with a₁ ≟ a₂ | b₁ ≟ b₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | yes refl | no ¬p    = no λ where refl → ¬p refl
  (_ ↦ _) ≟ unit    = no λ()
  unit    ≟ (_ ↦ _) = no λ()

  elems : ∀ Γ a → Enumerator (a ∈ Γ)
  elems [] a = ∅
  elems (b ∷ Γ) a with a ≟ b
  ... | yes refl = ‼ (here refl) ⟨∣⟩ (‼ there ⊛ elems Γ a)
  ... | no  ¬p   = ‼ there ⊛ elems Γ a

  elems-monotone : ∀ Γ a → Monotone (elems Γ a)
  elems-monotone (b ∷ Γ) .b {x = here refl} elem lq
    with b ≟ b
  ... | yes refl = here refl
  ... | no ¬p    = ⊥-elim (¬p refl)
  elems-monotone (b ∷ Γ) a {x = there x} elem lq
    with a ≟ b | elems-monotone Γ a {x = x} {!!} lq
  ... | yes refl | elem' = ∈-++⁺ʳ [ here refl ] (∈-++⁺ˡ (∈-map⁺ there elem'))
  ... | no _     | elem' = ∈-++⁺ˡ (∈-map⁺ there elem')

  elems-complete : ∀ Γ a → Complete (elems Γ a) 
  elems-complete (b ∷ Γ) .b {here refl}
    with b ≟ b
  ... | yes refl = ↑l 0 (here refl)
  ... | no  ¬p   = ⊥-elim (¬p refl)
  elems-complete (b ∷ Γ) a {there px}
    with a ≟ b | elems-complete Γ a {px}
  ... | yes refl | ↑l loc elem' = ↑l loc (∈-++⁺ʳ [ here refl ] (∈-++⁺ˡ (∈-map⁺ there elem')))
  ... | no _     | ↑l loc elem' = ↑l loc (∈-++⁺ˡ (∈-map⁺ there elem'))

  celems : ∀ Γ a → CEnumerator (a ∈ Γ)
  enum (celems Γ a) = elems Γ a
  mono (celems Γ a) = elems-monotone Γ a
  comp (celems Γ a) = elems-complete Γ a


  --concatMap (λ f → map f (enumerate' d₂ n)) (concatMap (λ f → map f (enumerate' d₁ n)) [ _,_ ])
  types : Enumerator Type
  types zero    = [ unit ]
  types (suc n) = [ unit ] ++
    concatMap (λ f → Data.List.map f (types n)) (concatMap (λ f → Data.List.map f (types n)) [ _↦_ ])

  product-equiv' : ∀ {A B : Set} {xs : List A} {ys : List B} (f : A → B → C) →
                    concatMap (λ f → Data.List.map f ys) (concatMap (λ f → Data.List.map f xs) [ f ]) ≡
                    cartesianProductWith f xs ys
  product-equiv' {xs = []} {ys} _ = refl --refl
  product-equiv' {xs = x ∷ xs} f
    = cong (λ xs → Data.List.map (f x) _ ++ xs )
        (product-equiv' {xs = xs} _) 

  types-monotone : Monotone types
  types-monotone {zero} {x = _ ↦ _} (here ()) lq
  types-monotone {zero} {x = _ ↦ _} (there ()) lq
  types-monotone {suc n} {suc m} {x = v@(a ↦ b)} (there px) (s≤s lq)
    with ∈-cartesianProductWith⁻ _↦_
           (types n) (types n) {v}
           (∈-resp-≡ (product-equiv' {xs = types n} _↦_) px)
  ... | .a , .b , el₁ , el₂ , refl
    = ∈-++⁺ʳ [ unit ]
        (∈-resp-≡ (sym (product-equiv' {xs = types m} _↦_))
          (∈-cartesianProductWith⁺ _↦_
             (types-monotone el₁ lq)
             (types-monotone el₂ lq)))
  types-monotone {n} {zero}  {x = unit} elem lq = here refl
  types-monotone {n} {suc m} {x = unit} elem lq = here refl

  types-complete : Complete types
  types-complete {a ↦ b}
    with types-complete {a} | types-complete {b}
  ... | ↑l loc₁ elem₁ | ↑l loc₂ elem₂
    = ↑l (suc (max loc₁ loc₂)) (∈-++⁺ʳ [ unit ]
              (∈-resp-≡ (sym (product-equiv' {xs = types (max loc₁ loc₂)} _↦_))
                (∈-cartesianProductWith⁺ _↦_
                  (types-monotone elem₁ (n≤maxnm loc₁ loc₂))
                  (types-monotone elem₂ (m≤maxnm loc₁ loc₂)))))
  types-complete {unit} = ↑l 0 (here refl)

  ctypes : CEnumerator Type
  enum ctypes = types
  mono ctypes = types-monotone
  comp ctypes = types-complete

  unitD : IDesc CEnumerator (Ctx × Type)
  unitD = `1

  identD : Ctx → Type → IDesc CEnumerator (Ctx × Type)
  identD Γ a = `Σ (a ∈ Γ) {celems Γ a} λ _ → `1

  absD : Ctx → Type → Type → IDesc CEnumerator (Ctx × Type)
  absD Γ a b = `var (a ∷ Γ , b)

  appD : Ctx → Type → IDesc CEnumerator (Ctx × Type)
  appD Γ b = `Σ Type {ctypes} λ a → `var (Γ , (a ↦ b)) `× `var (Γ , a)

  TermF : Func CEnumerator (Ctx × Type)
  out TermF (Γ , t@(a ↦ b)) = `σ 3 λ
    { zero             → identD Γ t
    ; (suc zero)       → absD Γ a b
    ; (suc (suc zero)) → appD Γ t }
  out TermF (Γ , t@unit)    = `σ 3 λ
    { zero             → unitD
    ; (suc zero)       → identD Γ unit
    ; (suc (suc zero)) → appD Γ unit
    }

  ctermf : ∀ a → CEnumerator (μ (mk (enums ∘ out TermF)) a)
  enum (ctermf a) = enumerate (mk (enums ∘ out TermF)) a
  mono (ctermf a) = monotone TermF a
  comp (ctermf a) = complete TermF a
