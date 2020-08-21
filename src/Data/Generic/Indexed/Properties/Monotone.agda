{-# OPTIONS --safe #-}

module Data.Generic.Indexed.Properties.Monotone where

open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Enumerate
open import Data.Unit hiding (_≤_)
open import Data.List
open import Data.Empty
open import Data.Fin

open import Data.Generic.Indexed.Universe
open import Data.Generic.Indexed.Enumerator

open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there)

open import Relation.Binary.PropositionalEquality using (refl ; cong ; cong₂ ; _≡_ ; sym ; trans)

open import Function using (_$_ ; const)
open import Function.Bundles

open import Function

module _ where

  -- membership respects propositional equality
  ∈-resp-≡ : ∀ {A : Set} {x : A} {xs ys} → xs ≡ ys → x ∈ xs → x ∈ ys
  ∈-resp-≡ refl el = el

  -- ⟨_⟩ is bijective
  open Inverse renaming (cong₂ to Icong₂)

  μ-iso : ∀ {F} {φ : Func F I} {i} → ⟦ out φ i ⟧ (μ φ) ↔ μ φ i
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

  -- Product equivalence, allows us to reuse lemmas from stdlib for cartesian product of
  -- lists. 
  --------------------------------------------------------------------------------------

  product-equiv : ∀ {A B : Set} {xs : List A} {ys : List B} →
                    concatMap (λ f → map f ys) (concatMap (λ f → map f xs) [ _,_ ]) ≡
                    cartesianProduct xs ys
  product-equiv {xs = []} {ys} = refl
  product-equiv {xs = x ∷ xs}  = cong (λ xs → map (x ,_) _ ++ xs) (product-equiv {xs = xs})


  ∈-Σ⁻ : ∀ {S : Set} {P : S → Set} {s : S} {p : P s} {xs : List S} {ys : (s : S) → List (P s)}
         → (s , p) ∈ concatMap (λ x → map (x ,_) (ys x)) xs → s ∈ xs × p ∈ ys s
         
  ∈-Σ⁻ {s = s} {xs = x ∷ xs} {ys} el with ∈-++⁻ (map (x ,_) (ys x)) el
  ∈-Σ⁻ {s = s} {xs = x ∷ xs} {ys} el | inj₁ x∈map with ∈-map⁻ _ x∈map
  ... | _ , p∈ys , refl = here refl , p∈ys
  ∈-Σ⁻ {s = s} {xs = x ∷ xs} {ys} el | inj₂ x∈com with ∈-Σ⁻ {xs = xs} x∈com
  ... | s∈xs , p∈ys = there s∈xs , p∈ys


  ∈-Σ⁺ : ∀ {S : Set} {P : S → Set} {s : S} {p : P s} {xs : List S} {ys : (s : S) → List (P s)}
         → s ∈ xs → p ∈ ys s → (s , p) ∈ concatMap (λ x → map (x ,_) (ys x)) xs
  ∈-Σ⁺ {xs = x ∷ xs} (here refl)  p∈ys = ∈-++⁺ˡ (∈-map⁺ _ p∈ys)
  ∈-Σ⁺ {xs = x ∷ xs} (there s∈xs) p∈ys = ∈-++⁺ʳ _ (∈-Σ⁺ s∈xs p∈ys)

  suc∉[zero] : ∀ {n : ℕ} {fn : Fin n} → Fin.suc fn ∈ [ zero ] → ⊥
  suc∉[zero] (here ())
  suc∉[zero] (there ())

  suc∈→n∈ : ∀ {n : ℕ} {fn : Fin n} {xs : List (Fin n)} → (Fin.suc fn) ∈ ([ zero ] ++ concatMap (λ f → map f xs) [ suc ]) → fn ∈ xs
  suc∈→n∈ el with ∈-++⁻ [ zero ] el
  suc∈→n∈ el | inj₁ x = ⊥-elim (suc∉[zero] x)
  suc∈→n∈ {xs = xs} el | inj₂ y with ∈-map⁻ suc (∈-resp-≡ (++-identityʳ _) y) 
  ... | _ , fn∈ , refl = fn∈

  ef-monotone : ∀ {n} → Monotone (enumerateFin n)
  ef-monotone {.(suc _)} {x = zero} _ _ = here refl
  ef-monotone {(suc n)} {x = suc x} el lq with ef-monotone {n} {x = x} (suc∈→n∈ el) lq
  ... | r = ∈-++⁺ʳ [ zero ] (∈-++⁺ˡ {ys = []} (∈-map⁺ suc r))


  monotone : ∀ {φ : Func Σ-info I} {d : IDesc Σ-info I} → Monotone (enumerate {φ = mk (enums ∘ out φ)} (enums d))
  
  monotone {d = d₁ `× d₂} el lq
    = ∈-resp-≡ (sym (product-equiv {xs = enumerate (enums d₁) _}))
               (∈-cartesianProduct⁺
                 (monotone {d = d₁} (proj₁ (∈-cartesianProduct⁻ (enumerate (enums d₁) _) (enumerate (enums d₂) _)
                   (∈-resp-≡ (product-equiv {xs = enumerate (enums d₁) _}) el))) lq)
                 (monotone {d = d₂} (proj₂ (∈-cartesianProduct⁻ (enumerate (enums d₁) _) (enumerate (enums d₂) _)
                   (∈-resp-≡ (product-equiv {xs = enumerate (enums d₁) _}) el))) lq))
                   
  monotone {d = `1} (here refl) lq = here refl
  
  monotone {φ = φ} {d = `var i} {suc n} {x = ⟨ x ⟩} el (s≤s lq)
    with monotone {d = out φ i} {x = x} (elem-inv μ-iso el) lq
  ... | r = ∈-map⁺ (⟨_⟩) r
  
  monotone {d = `σ n f} {x = fn , x} el lq
    with ef-monotone {n} {x = fn} (proj₁ (∈-Σ⁻ el) ) lq
       | monotone {d = f fn} {x = x} (proj₂ (∈-Σ⁻ {xs = enumerateFin _ _} el)) lq
  ... | fn∈ | x∈ = ∈-Σ⁺ fn∈ x∈
  
  monotone {d = `Σ S {si} f} {x = s , x} el lq
    with Σ-monotone si (proj₁ (∈-Σ⁻ el)) lq
       | monotone {d = f s} {x = x} (proj₂ (∈-Σ⁻ {xs = E si _} el)) lq
  ... | s∈ | x∈ = ∈-Σ⁺ s∈ x∈
