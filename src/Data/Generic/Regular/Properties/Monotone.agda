module Data.Generic.Regular.Properties.Monotone where

open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Enumerate
open import Data.Unit hiding (_≤_)
open import Data.List

open import Data.Generic.Regular.Universe
open import Data.Generic.Regular.Enumerator

open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there)

open import Relation.Binary.PropositionalEquality using (refl ; cong ; _≡_ ; sym ; trans)

open import Function.Bundles

module _ where 

  ‼-⊛ : ∀ {A B : Set} → (A → B) → List A → List B
  ‼-⊛ f xs = concatMap (λ f → Data.List.map f xs) [ f ]


  open Inverse

  μ-iso : ∀ {d} → ⟦ d ⟧ (μ d) ↔ μ d
  f   μ-iso x = ⟨ x ⟩ 
  f⁻¹ μ-iso ⟨ x ⟩ = x

  cong₁ μ-iso refl = refl
  cong₂ μ-iso refl = refl
  
  proj₁ (inverse μ-iso) ⟨ x ⟩     = refl
  proj₂ (inverse μ-iso) _  = refl

  elem-inv : ∀ (inj : R₁ ↔ R₂) {x xs} →
               f inj x ∈ ‼-⊛ (f inj) xs → 
               x ∈ xs
  elem-inv inj {xs = x ∷ xs} (here px ) = here (trans (sym (proj₂ (inverse inj) _))
                                           (trans (cong (f⁻¹ inj) px)
                                                  (proj₂ (inverse inj) _))
                                                  )
  elem-inv inj {xs = x ∷ xs} (there px) = there (elem-inv inj px)

  ‼-⊛-inv : ∀ (inj : R₁ ↔ R₂) 
               {e : REnum R₁ P} {er : IEnum P} {x} →
               (‼ (f inj) ⊛ e) (fix er) ↝ f inj x →
               e               (fix er) ↝ x 
  loc (‼-⊛-inv inj {e} {er} px)  = loc px
  elem (‼-⊛-inv inj {e} {er} px) = elem-inv inj (elem px)

  ≤-decr : ∀ n m → suc n ≤ m → n ≤ m
  ≤-decr zero .(suc _) (s≤s leq) = z≤n
  ≤-decr (suc n) .(suc _) (s≤s leq) = s≤s (≤-decr n _ leq)

  ≤m→msuc : ∀ n m → suc n ≤ m → ∃ λ m' → m ≡ suc m'
  ≤m→msuc n (suc m) x = m , refl

  postulate 
    lemma : ∀ {d n x} → fix (enumerate-μ (enums ⟨$⟩ d)) tt ⟨ suc n ⟩↝ ⟨ x ⟩ →
                            (enumerate (enums ⟨$⟩ d)) (fix (enumerate-μ (enums ⟨$⟩ d))) ⟨ n ⟩↝ x

  ∈-resp-≡ : ∀ {A B : Set} {xs ys : List A}{x} → xs ≡ ys → x ∈ xs → x ∈ ys
  ∈-resp-≡ refl px = px

  -- Monotonicity of `enumerate`
  postulate
    monotone : (d d' : Desc (Σ Set k-info)) →
                       Monotone (enumerate   (enums ⟨$⟩ d))
                                (enumerate-μ (enums ⟨$⟩ d'))               

  -- monotone (d `∪ d₁) d' n m x elem leq = {!x!}
  -- monotone (d `× d₁) d' n m x elem leq = {!n!}
  -- monotone `var d' (suc n) m ⟨ x ⟩ elem leq with monotone d' d' n m x (lemma elem) (≤-decr n m leq) | ≤m→msuc n m leq
  -- ... | r | _ , refl = ∈-++⁺ˡ {ys = []} (∈-map⁺ ⟨_⟩ (∈-resp-≡ {B = μ (proj₁ ⟨$⟩ d')} {!!} r))
  -- monotone `1        d' n m x elem leq = elem
  -- monotone (`k (S , ki))   d'          = {!!}
  

  -- ismonotone : ∀ d → IsMonotone (enumerate-μ (enums ⟨$⟩ d))
  -- ismonotone d n m ⟨ v ⟩ elem lq
  --   with monotone d d n m v
  --        (proj₂ (loc (‼-⊛-inv μ-iso {enumerate (enums ⟨$⟩ d)}
  --                    (↑l (n , elem))))
  --        ) lq
  -- ... | elem' = ∈-++⁺ˡ (∈-map⁺ ⟨_⟩ elem')
  
