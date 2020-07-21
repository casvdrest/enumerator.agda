
module Data.Generic.Regular.Properties.Complete where

open import Data.List
open import Data.Enumerate
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Unit hiding (_≤_)

open import Data.Generic.Regular.Universe
open import Data.Generic.Regular.Enumerator
open import Data.Generic.Regular.Properties.Monotone

open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there)

open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; inspect)

open import Function.Bundles

module _ where 
  
  open Inverse

  variable
    n m : ℕ

  x∈-resp-≡ : ∀ {A : Set} {x y : A} {xs} → x ≡ y → x ∈ xs → y ∈ xs
  x∈-resp-≡ refl x = x


  prod-inv : ∀ (inj : R₁ ↔ R₂) {e : REnum R₁ P} {er : IEnum P} {x} →
               (‼ (f inj) ⊛ e) (fix er) ↝ x →
               ------------------------------------
               e               (fix er) ↝ f⁻¹ inj x
               
  loc  (prod-inv inj {e} {er}     px) = loc px
  elem (prod-inv inj {e} {er} {x} px) = elem-inv inj (x∈-resp-≡ (sym (proj₁ (inverse inj) x)) (elem px)) 


  mono-map : ∀ (inj : R₁ ↔ R₂) {e : REnum R₁ P} {er : IEnum P} →
               Monotone e er →
               ---------------------------
               Monotone (‼ (f inj) ⊛ e) er
               
  mono-map inj {e} {er} mt n m x el lq = inv-map-elem (mt n m (f⁻¹ inj x) (elem (prod-inv inj {e} (↑l _ el))) lq)

    where inv-map-elem : ∀ {x xs} →
                         f⁻¹ inj x ∈ xs → 
                         ------------------
                         x ∈ ‼-⊛ (f inj) xs
                         
          inv-map-elem (here refl) = here  (sym (proj₁ (inverse inj) _))
          inv-map-elem (there px ) = there (inv-map-elem px)


  prod-map : ∀ (f : R₁ → R₂) {e : REnum R₁ P} {er : IEnum P} {x} →
               e (fix er) ⟨ n ⟩↝ x →
               ------------------------------
               (‼ f ⊛ e) (fix er) ⟨ n ⟩↝ f x
               
  prod-map _ = ‼-⊛-elem
  
    where ‼-⊛-elem : ∀ {A B : Set} {f : A → B} {x xs} →
                       x ∈ xs →
                       -----------------------
                       f x ∈ ‼-⊛ f xs
                       
          ‼-⊛-elem (here refl) = here refl
          ‼-⊛-elem (there p)   = there (‼-⊛-elem p)


  -- Enumerator choice produces all of same the element that its left
  -- operand produces
  ⟨∣⟩-complete-left : ∀ {e₁ e₂ : REnum R P} {er x} →
                      e₁          (fix er) ↝ x →
                      ------------------------------
                      (e₁ ⟨∣⟩ e₂) (fix er) ↝ x
                      
  loc  (⟨∣⟩-complete-left px) = loc px
  elem (⟨∣⟩-complete-left px) = ∈-++⁺ˡ (elem px)


-- Enumerator choice produces all of same the element that its left
  -- operand produces
  ⟨∣⟩-complete-right : ∀ {e₁ e₂ : REnum R P} {er x} →
                      e₂ (fix er) ↝ x →
                      -------------------------------
                      (e₁ ⟨∣⟩ e₂) (fix er) ↝ x
                      
  loc  (⟨∣⟩-complete-right px) = loc px
  elem (⟨∣⟩-complete-right px) = ∈-++⁺ʳ _ (elem px)

  
  -- ⊛-complete : ∀ {e₁ : REnum (R₁ → R₂) P}
  --                {e₂ : REnum R₁ P}
  --                {er f x n} →
  --                Produces e₁ er f n → 
  --                Produces e₂ er x n → 
  --                Produces (e₁ ⊛ e₂) er (f x) n
  -- prod (⊛-complete {e₁ = e₁} {e₂} {er} {n = n} pr₁ pr₂)
  --   with enum e₁ (fix er) n
  --      | enum e₂ (fix er) n
  --      | prod pr₁
  --      | prod pr₂
  -- ... | x ∷ xs | y ∷ ys | px | qx = ap-complete px qx

  --   where ap-complete : ∀ {A B : Set}
  --                         {f : A → B} {fs}
  --                         {x : A} {xs} →
  --                         f ∈ fs → x ∈ xs →
  --                         f x ∈ concatMap (λ f → Data.List.map f xs) fs
  --         ap-complete (here refl) qx = ∈-++⁺ˡ (∈-map⁺ _ qx)
  --         ap-complete (there px)  qx = ∈-++⁺ʳ _ (ap-complete px qx)
  
  -- postulate var-complete : ∀ {d v n} → v ∈ (enumerate d) (fix (enumerate-μ d)) n → ⟨ v ⟩ ∈ fix (enumerate-μ d) tt (suc n)

  -- max : (n m : ℕ) → ℕ
  -- max zero    m       = m
  -- max (suc n) zero    = suc n
  -- max (suc n) (suc m) = suc (max n m)

  -- ≤-refl : ∀ n → n ≤ n
  -- ≤-refl zero    = z≤n
  -- ≤-refl (suc n) = s≤s (≤-refl n)

  -- ≤-max-left : ∀ n m → n ≤ max n m
  -- ≤-max-left zero    m       = z≤n
  -- ≤-max-left (suc n) zero    = ≤-refl (suc n)
  -- ≤-max-left (suc n) (suc m) = s≤s (≤-max-left n m)
  
  -- ≤-max-right : ∀ n m → m ≤ max n m 
  -- ≤-max-right zero    m       = ≤-refl m
  -- ≤-max-right (suc n) zero    = z≤n
  -- ≤-max-right (suc n) (suc m) = s≤s (≤-max-right n m)


  -- -- Commpleteness of `enumerate`
  -- complete : (d d' : Desc (Σ Set k-info)) →
  --            Complete (enumerate   (enums ⟨$⟩ d))
  --                     ( enumerate-μ (enums ⟨$⟩ d'))
  -- complete (d₁ `∪ d₂) _ (inj₁ x) with complete d₁ _ x
  -- ... | n , px
  --   = n , ⟨∣⟩-complete-left (prod-map inj₁ n px)
  -- complete (d₁ `∪ d₂) _ (inj₂ y) with complete d₂ _ y
  -- ... | n , px
  --   = n , ⟨∣⟩-complete-right {e₁ = ‼ inj₁ ⊛ enumerate (enums ⟨$⟩ d₁)}
  --                            (prod-map inj₂ n px)                                  
  -- complete (d₁ `× d₂) _ (x , y) with complete d₁ _ x | complete d₂ _ y
  -- ... | n , px | m , qx
  --   = max n m , ⊛-complete (prod-map _,_ (max n m)
  --                            (monotone d₁ _ px (≤-max-left n m)))
  --                          (monotone d₂ _ qx (≤-max-right n m))
  -- complete `var d' ⟨ x ⟩ with complete d' d' x
  -- ... | n , record { prod = pr } = suc n , record { prod = var-complete pr  }
  -- complete `1 _  tt
  --   = 0 , record { prod = here refl } 
  -- complete (`k (S , ki)) _ x with k-complete ki x
  -- ... | n , px
  --   = n , record { prod = prod px }


  -- iscomplete : ∀ d → IsComplete (enumerate-μ (enums ⟨$⟩ d))
  -- iscomplete d tt ⟨ x ⟩ with complete d d x
  -- ... | n , p = n , prod-map _ _ p
