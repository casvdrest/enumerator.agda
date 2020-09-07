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
open import Data.List.Properties

open import Function
open import Function.Bundles

open import Relation.Binary.PropositionalEquality renaming (cong₂ to pCong₂ ; [_] to P[_])
open import Relation.Nullary
open import Relation.Unary hiding (_∈_ ; ∅)

-- Intrinsically-typed syntax for the simply-typed λ-calculus
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


-- A certified enumerator for list membership proofs
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

  celems : ∀ Γ a → CEnumerator (a ∈ Γ)
  enum (celems Γ a) = elems Γ a
  mono (celems Γ a) = elems-monotone Γ a
  comp (celems Γ a) = elems-complete Γ a


-- A certified enumerator for types
module _ where 

  types : Enumerator Type
  types zero    = [ unit ]
  types (suc n) = [ unit ] ++
    concatMap (λ f → Data.List.map f (types n))
      (concatMap (λ f → Data.List.map f (types n)) [ _↦_ ])


  product-equiv' : ∀ {A B : Set} {xs : List A} {ys : List B} (f : A → B → C) →
                    concatMap (λ f → Data.List.map f ys)
                      (concatMap (λ f → Data.List.map f xs) [ f ]) ≡
                    cartesianProductWith f xs ys
  product-equiv' {xs = []} {ys} _ = refl 
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


-- A generic description of the simply-typed λ-calculus
module _ where 

  unitD : IDesc CEnumerator (Ctx × Type)
  unitD = `1

  identD : Ctx → Type → IDesc CEnumerator (Ctx × Type)
  identD Γ a = `Σ (a ∈ Γ) {celems Γ a} λ _ → `1

  absD : Ctx → Type → Type → IDesc CEnumerator (Ctx × Type)
  absD Γ a b = `var (a ∷ Γ , b)

  appD : Ctx → Type → IDesc CEnumerator (Ctx × Type)
  appD Γ b = `Σ Type {ctypes} λ a → `var (Γ , (a ↦ b)) `× `var (Γ , a)


  TermF : Func CEnumerator (Ctx × Type)
  out TermF (Γ , t) = `σ 3 λ
    { zero             → identD Γ t
    ; (suc zero)       → appD Γ t
    ; (suc (suc zero)) →
         case t of λ
           { (a ↦ b) → absD Γ a b
           ; unit    → unitD
           }
    }



-- TermF describes 'Term' (i.e., its fixpoint is isomorphic to 'Term')
module _ where 

  open Inverse

  TermF↔Term : ∀ {Γ a} → μ (mk (enums ∘ out TermF)) (Γ , a) ↔ Term Γ a
  
  f          TermF↔Term              ⟨ zero , a∈Γ , tt ⟩          = ident a∈Γ
  f          TermF↔Term              ⟨ suc zero , a , tm₁ , tm₂ ⟩ = app (f TermF↔Term tm₁) (f TermF↔Term tm₂)
  Inverse.f (TermF↔Term {a = a ↦ b}) ⟨ suc (suc zero) , tm ⟩      = abs (f TermF↔Term tm)
  Inverse.f (TermF↔Term {a = unit }) ⟨ suc (suc zero) , tt ⟩      = tt

  f⁻¹ TermF↔Term tt            = ⟨ suc (suc zero) , tt ⟩
  f⁻¹ TermF↔Term (ident a∈Γ)   = ⟨ zero , a∈Γ , tt ⟩
  f⁻¹ TermF↔Term (abs tm)      = ⟨ suc (suc zero) , f⁻¹ TermF↔Term tm ⟩
  f⁻¹ TermF↔Term (app tm₁ tm₂) = ⟨ (suc zero , _ , (f⁻¹ TermF↔Term tm₁) , f⁻¹ TermF↔Term tm₂) ⟩
  
  cong₁ TermF↔Term refl = refl
  cong₂ TermF↔Term refl = refl

  proj₁ (inverse TermF↔Term)               tt = refl
  proj₁ (inverse (TermF↔Term {a = _ ↦ _})) (ident x)     = refl
  proj₁ (inverse (TermF↔Term {a = unit })) (ident x)     = refl
  proj₁ (inverse TermF↔Term)               (abs tm)
    = cong abs (proj₁ (inverse TermF↔Term) tm)
  proj₁ (inverse (TermF↔Term {a = _ ↦ _})) (app tm₁ tm₂)
    = pCong₂ app (proj₁ (inverse TermF↔Term) tm₁) (proj₁ (inverse TermF↔Term) tm₂)
  proj₁ (inverse (TermF↔Term {a = unit })) (app tm₁ tm₂)
    = pCong₂ app (proj₁ (inverse TermF↔Term) tm₁) (proj₁ (inverse TermF↔Term) tm₂)
  
  proj₂ (inverse (TermF↔Term {a = _ ↦ _})) ⟨ zero , a∈Γ , tt ⟩          = refl
  proj₂ (inverse (TermF↔Term {a = unit })) ⟨ zero , a∈Γ , tt ⟩          = refl
  proj₂ (inverse (TermF↔Term {a = _ ↦ _})) ⟨ suc zero , _ , tm₁ , tm₂ ⟩
    = pCong₂ (λ x y → ⟨ suc zero , _ , x , y ⟩) (proj₂ (inverse TermF↔Term) tm₁) (proj₂ (inverse TermF↔Term) tm₂)
  proj₂ (inverse (TermF↔Term {a = unit })) ⟨ suc zero , _ , tm₁ , tm₂ ⟩
    = pCong₂ (λ x y → ⟨ suc zero , _ , x , y ⟩) (proj₂ (inverse TermF↔Term) tm₁) (proj₂ (inverse TermF↔Term) tm₂)
  proj₂ (inverse (TermF↔Term {a = _ ↦ _})) ⟨ suc (suc zero) , tm ⟩
    = cong (λ x → ⟨ suc (suc zero) , x ⟩) (proj₂ (inverse TermF↔Term) tm)
  proj₂ (inverse (TermF↔Term {a = unit })) ⟨ suc (suc zero) , tt ⟩      = refl


-- Certified enumerators respect type isomorphisms
module _ where 

  open Inverse

  ap-iso : A ↔ B → Enumerator A → Enumerator B
  ap-iso iso e n = Data.List.map (f iso) (e n)

  mono-resp-↔ : ∀ {e} → (iso : A ↔ B) → Monotone e → Monotone (ap-iso iso e)
  mono-resp-↔ iso mn {x = y} elem lq
    with f⁻¹ iso y | inspect (f⁻¹ iso) y | proj₁ (inverse iso) y
  mono-resp-↔ iso mn {x = y} elem lq
    | x | P[ eq₁ ] | eq₂ rewrite eq₁ | sym eq₂ with mn {x = x} (elem-inv iso elem) lq
  ... | elem' = ∈-map⁺ (f iso) elem'

  comp-resp-↔ : ∀ {e} → (iso : A ↔ B) → Complete e → Complete (ap-iso iso e)
  loc (comp-resp-↔ iso cp {x}) = loc {x = f⁻¹ iso x} cp
  elem (comp-resp-↔ iso cp {x = y})
    with f⁻¹ iso y | inspect (f⁻¹ iso) y | proj₁ (inverse iso) y 
  ... | x | P[ eq₁ ] | eq₂ rewrite eq₁ | sym eq₂ = ∈-map⁺ (f iso) (elem cp)

  enum-resp-↔ : A ↔ B → CEnumerator A → CEnumerator B
  enum (enum-resp-↔ iso ce) = ap-iso iso (enum ce)
  mono (enum-resp-↔ iso ce) = mono-resp-↔ iso (mono ce)
  comp (enum-resp-↔ iso ce) = comp-resp-↔ iso (comp ce)


-- A certified enumerator for the simply-typed λ-calculus
module _ where

  open import Data.Generic.Indexed.CertifiedEnumerator

  terms : (Γ : Ctx) → (a : Type) → CEnumerator (Term Γ a) 
  terms Γ a = enum-resp-↔ TermF↔Term (cenumerate TermF (Γ , a))
