{-# OPTIONS --safe #-}

module Data.Simple.Enumerator where

open import Data.Unit
open import Data.Sum
open import Data.Nat
open import Data.Empty

open import Data.Simple.Universe
open import Data.Enumerate

open import Data.Product

open import Data.List
open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; cong₂ ; inspect ; trans)

open import Function.Bundles

module _ where

  enumerate : ∀ {u'} → (u : U) → REnum {⊤} (⟦ u ⟧ (μ u')) λ where tt → ⟦ u' ⟧ (μ u')  
  enumerate `1         =  ‼ tt
  enumerate `var       =  ‼ ⟨_⟩ ⊛ var tt
  enumerate (u₁ `+ u₂) =  ‼ inj₁ ⊛ enumerate u₁ ⟨∣⟩
                          ‼ inj₂ ⊛ enumerate u₂

  enumerate-μ : ∀ u → Enum (μ u)
  enumerate-μ u tt μ n = Data.List.map ⟨_⟩ (enumerate u (fix λ _ → enumerate u) n)

  
  ‼-⊛ : ∀ {A B : Set} → (A → B) → List A → List B
  ‼-⊛ f xs = concatMap (λ f → Data.List.map f xs) [ f ]

  μ-iso : ∀ {d} → ⟦ d ⟧ (μ d) ↔ μ d
  Inverse.f   μ-iso x = ⟨ x ⟩ 
  Inverse.f⁻¹ μ-iso ⟨ x ⟩ = x

  Inverse.cong₁ μ-iso refl = refl
  Inverse.cong₂ μ-iso refl = refl
  
  proj₁ (Inverse.inverse μ-iso) ⟨ x ⟩     = refl
  proj₂ (Inverse.inverse μ-iso) _  = refl

  elem-inv : ∀ (inj : R₁ ↔ R₂) {x xs} →
               Inverse.f inj x ∈ ‼-⊛ (Inverse.f inj) xs → 
               x ∈ xs
  elem-inv inj {xs = x ∷ xs} (here px ) =
    here (trans (sym (proj₂ (Inverse.inverse inj) _))
         (trans (cong (Inverse.f⁻¹ inj) px)
                (proj₂ (Inverse.inverse inj) _)) )
  elem-inv inj {xs = x ∷ xs} (there px) = there (elem-inv inj px)

  ‼-⊛-inv : ∀ (inj : R₁ ↔ R₂) 
               {e : REnum R₁ P} {er : IEnum P} {x} →
               (‼ (Inverse.f inj) ⊛ e) (fix er) ↝ Inverse.f inj x →
               e               (fix er) ↝ x 
  loc (‼-⊛-inv inj {e} {er} px)  = loc px
  elem (‼-⊛-inv inj {e} {er} px) = elem-inv inj (elem px)

  ∈-resp-≡ : ∀ {A : Set} {x} {xs ys : List A} → xs ≡ ys → x ∈ xs → x ∈ ys
  ∈-resp-≡ refl el = el

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

  inj₁-inv : ∀ {A B : Set} {n} (e₁ : REnum A P) (e₂ : REnum B P) {er} {x : A} →
               inj₁ x ∈ (‼ inj₁ ⊛ e₁ ⟨∣⟩ ‼ inj₂ ⊛ e₂) er n → x ∈ e₁ er n
  inj₁-inv {n = n} e₁ e₂ {er} el with ∈-++⁻ ((‼ inj₁ ⊛ e₁) er n) el
  ... | inj₁ x = map-inj₁-inv (∈-resp-≡ (++-identityʳ _) x) 
  ... | inj₂ y = ⊥-elim (inj₁≠inj₂ (∈-resp-≡ (++-identityʳ _) y))

  inj₂-inv : ∀ {A B : Set} {n} (e₁ : REnum A P) (e₂ : REnum B P) {er} {y : B} →
               inj₂ y ∈ (‼ inj₁ ⊛ e₁ ⟨∣⟩ ‼ inj₂ ⊛ e₂) er n → y ∈ e₂ er n
  inj₂-inv {n = n} e₁ e₂ {er} el with ∈-++⁻ ((‼ inj₁ ⊛ e₁) er n) el 
  ... | inj₁ x = ⊥-elim (inj₂≠inj₁ (∈-resp-≡ (++-identityʳ _) x))
  ... | inj₂ y = map-inj₂-inv (∈-resp-≡ (++-identityʳ _) y)

  enumerate-wb₁ : ∀ n m k u u' x →
                    x ∈ enumerate u (ffix (n , λ μ _ → enumerate u' μ) λ _ _ → []) m → 
                    x ∈ enumerate u (ffix (n , λ μ _ → enumerate u' μ) λ _ _ → []) k
  enumerate-wb₁ n m k `1 u' .tt (here refl) = here refl
  enumerate-wb₁ (suc n) m k `var u' ⟨ x ⟩ el
    with enumerate-wb₁ n m k u' u' x (elem-inv μ-iso el)
  ... | r = ∈-++⁺ˡ (∈-map⁺ ⟨_⟩ r)
  enumerate-wb₁ n m k (u₁ `+ u₂) u' (inj₁ x) el
    with enumerate-wb₁ n m k u₁ u' x (inj₁-inv (enumerate u₁) (enumerate u₂) el)
  ... | r = ∈-++⁺ˡ (∈-++⁺ˡ (∈-map⁺ inj₁ r))
  enumerate-wb₁ n m k (u₁ `+ u₂) u' (inj₂ y) el
    with enumerate-wb₁ n m k u₂ u' y (inj₂-inv (enumerate u₁) (enumerate u₂) el)
  ... | r = ∈-++⁺ʳ (Data.List.map inj₁ (enumerate u₁ _ _) ++ []) (∈-++⁺ˡ {ys = []} (∈-map⁺ inj₂ r))

  enumerate-wb₂ : ∀ {u'} u n →
                   enumerate u (fix (λ _ → enumerate u')) n ≡
                   enumerate u (ffix (n , λ μ _ → enumerate u' μ) (λ _ _ → [])) n
  enumerate-wb₂ `1 n = refl
  enumerate-wb₂ `var n = refl
  enumerate-wb₂ {u'} (u₁ `+ u₂) n with enumerate-wb₂ {u'} u₁ n | enumerate-wb₂ {u'} u₂ n
  ... | r₁ | r₂ = cong₂ (λ xs ys → (Data.List.map inj₁ xs ++ []) ++ Data.List.map inj₂ ys ++ []) r₁ r₂

  fix-step : ∀ {u' x n} → x ∈ enumerate u' (fix (λ _ → enumerate u')) n
                     → x ∈ fix (λ _ → enumerate u') tt (suc n)
  fix-step {u'} {v} {n} el = enumerate-wb₁ n n (suc n) u' u' v (∈-resp-≡ (enumerate-wb₂ u' n) el)


  complete : ∀ {u'} → (u : U) →
               Complete (enumerate u) λ _ → enumerate u'

  loc  (complete `1)           = 0
  elem (complete `1)           = here refl

  loc  (complete `var {⟨ x ⟩}) = suc (loc (complete _ {x}))
  elem (complete `var {⟨ x ⟩}) with fix-step (elem (complete _ {x})) 
  ... | p = ∈-++⁺ˡ {ys = []} (∈-map⁺ ⟨_⟩ p)

  loc  (complete (u₁ `+ u₂) {inj₁ x}) = loc (complete u₁)
  elem (complete (u₁ `+ u₂) {inj₁ x}) = ∈-++⁺ˡ (∈-++⁺ˡ (∈-map⁺ inj₁ (elem (complete u₁))))
  loc  (complete (u₁ `+ u₂) {inj₂ y}) = loc (complete u₂)
  elem (complete (u₁ `+ u₂) {inj₂ y}) = ∈-++⁺ʳ (Data.List.map inj₁ (enumerate _ _ _) ++ [])
                                               (∈-++⁺ˡ (∈-map⁺ inj₂ (elem (complete u₂)))) 


  iscomplete : ∀ u → IsComplete (enumerate-μ u)
  loc  (iscomplete u {_} {⟨ x ⟩}) = loc (complete u {x})
  elem (iscomplete u {_} {⟨ x ⟩}) = (∈-map⁺ ⟨_⟩ (elem (complete u {x})))
 
