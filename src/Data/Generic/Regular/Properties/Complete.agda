module Data.Generic.Regular.Properties.Complete where

open import Data.List
open import Data.Enumerate
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.Unit hiding (_≤_)
open import Data.Empty

open import Data.Generic.Regular.Universe
open import Data.Generic.Regular.Enumerator
open import Data.Generic.Regular.Properties.Monotone

open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there)

open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; inspect ; cong₂ ; trans)

open import Function.Bundles
open import Function using (const ; id ; _$_)

module _ where

  ∈-resp-≡ : ∀ {A : Set} {x} {xs ys : List A} → xs ≡ ys → x ∈ xs → x ∈ ys
  ∈-resp-≡ refl el = el

  -----------------------------------------------------------------------------------------------------------------
  -- Some helper lemmas about the behaviour of coproduct enumerators 

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


  -----------------------------------------------------------------------------------------------------------------
  -- Some helper lemmas about the behaviour of product enumerators

  ap-complete : ∀ {A B : Set}
                  {f : A → B} {fs}
                  {x : A} {xs} →
                  f ∈ fs → x ∈ xs →
                  f x ∈ concatMap (λ f → map f xs) fs
  ap-complete (here refl) qx = ∈-++⁺ˡ (∈-map⁺ _ qx)
  ap-complete (there px)  qx = ∈-++⁺ʳ _ (ap-complete px qx)

  product-equiv : ∀ {A B : Set} {xs : List A} {ys : List B} →
                    concatMap (λ f → map f ys) (concatMap (λ f → map f xs) [ _,_ ]) ≡
                    cartesianProduct xs ys
  product-equiv {xs = []}     = refl
  product-equiv {xs = x ∷ xs} = cong (λ xs → map (x ,_) _ ++ xs) (product-equiv {xs = xs})

  fst-inv : ∀ {A B : Set} {n} (e₁ : REnum A P) (e₂ : REnum B P) {er} {x : A} {y : B} →
              (x , y) ∈ (‼ _,_ ⊛ e₁ ⊛ e₂) er n → x ∈ e₁ er n
  fst-inv {n = n} e₁ e₂ {er} el = proj₁ (∈-cartesianProduct⁻ (e₁ er n) (e₂ er n)
                                                             (∈-resp-≡ (product-equiv {xs = e₁ _ _} {e₂ _ _}) el))

  snd-inv : ∀ {A B : Set} {n} (e₁ : REnum A P) (e₂ : REnum B P) {er} {x : A} {y : B} →
              (x , y) ∈ (‼ _,_ ⊛ e₁ ⊛ e₂) er n → y ∈ e₂ er n
  snd-inv {n = n} e₁ e₂ {er} el = proj₂ ((∈-cartesianProduct⁻ (e₁ er n) (e₂ er n)
                                                              (∈-resp-≡ (product-equiv {xs = e₁ _ _} {e₂ _ _}) el)))

  prod-elem : ∀ {A B : Set} {n} (e₁ : REnum A P) (e₂ : REnum B P) {er} {x : A} {y : B} →
              x ∈ e₁ er n → y ∈ e₂ er n → 
              (x , y) ∈ (‼ _,_ ⊛ e₁ ⊛ e₂) er n
  prod-elem {n = n} e₁ e₂ {er} el₁ el₂ = ap-complete (ap-complete {fs = [ _,_ ]} (here refl) el₁) el₂

  max : ℕ → ℕ → ℕ
  max zero    m       = m
  max (suc n) zero    = suc n
  max (suc n) (suc m) = suc (max n m)

  ≤-refl : ∀ n → n ≤ n
  ≤-refl zero    = z≤n
  ≤-refl (suc n) = s≤s (≤-refl n)

  n≤maxnm : ∀ n m → n ≤ max n m
  n≤maxnm zero    m       = z≤n
  n≤maxnm (suc n) zero    = ≤-refl (suc n)
  n≤maxnm (suc n) (suc m) = s≤s (n≤maxnm n m)

  m≤maxnm : ∀ n m → m ≤ max n m
  m≤maxnm zero    m       = ≤-refl m
  m≤maxnm (suc n) zero    = z≤n
  m≤maxnm (suc n) (suc m) = s≤s (m≤maxnm n m)
  
  -----------------------------------------------------------------------------------------------------------------
  -- Well-behavedness part 1: `enumerate` uses the recursive argument `μ` for every recursive call

  enumerate-wb₁ : ∀ n m k d d' x →
                    x ∈ enumerate {enums d'} (enums d) (ffix (n , λ μ _ → enumerate (enums d') μ) λ _ _ → []) m →
                    m ≤ k → 
                    x ∈ enumerate            (enums d) (ffix (n , λ μ _ → enumerate (enums d') μ) λ _ _ → []) k
                    
  enumerate-wb₁ n m k (d₁ `∪ d₂) d' (inj₁ x) el lq
    with enumerate-wb₁ n m k d₁ d' x
                      (inj₁-inv (enumerate (enums d₁))
                                (enumerate (enums d₂)) el) lq 
  ... | r = ∈-++⁺ˡ (∈-++⁺ˡ (∈-map⁺ inj₁ r))
  enumerate-wb₁ n m k (d₁ `∪ d₂) d' (inj₂ y) el lq
    with enumerate-wb₁ n m k d₂ d' y
                       (inj₂-inv (enumerate (enums d₁))
                                 (enumerate (enums d₂)) el) lq
  ... | r = ∈-++⁺ʳ (Data.List.map inj₁ (enumerate (enums d₁) _ _) ++ [])
                   (∈-++⁺ˡ {ys = []} (∈-map⁺ inj₂ r))
  
  enumerate-wb₁ n m k (d₁ `× d₂) d' (x , y) el lq
    with enumerate-wb₁ n m k d₁ d' x
                       (fst-inv (enumerate (enums d₁))
                                (enumerate (enums d₂)) el) lq
       | enumerate-wb₁ n m k d₂ d' y
                       (snd-inv (enumerate (enums d₁))
                                (enumerate (enums d₂)) el) lq
  ... | r₁ | r₂ = prod-elem (enumerate (enums d₁))
                            (enumerate (enums d₂)) r₁ r₂
  
  enumerate-wb₁ (suc n) m k `var d' ⟨ x ⟩ el lq
    with enumerate-wb₁ n m k d' d' x
                      (elem-inv μ-iso el) lq
  ... | r = ∈-++⁺ˡ (∈-map⁺ ⟨_⟩ r)
  
  enumerate-wb₁ n m k `1          d' tt el lq = here refl
  enumerate-wb₁ n m k (`k S {ki}) d' v  el lq = k-monotone ki m k _ el lq


  -----------------------------------------------------------------------------------------------------------------
  -- Well-behavedness part 2: `enumerate` uses the given size parameter `n` to fuel `ffix`

  enumerate-wb₂ : ∀ {d'} d n →
                    enumerate {d'} d (fix (λ _ → enumerate d')) n ≡
                    enumerate      d (ffix (n , λ μ _ → enumerate d' μ) (λ _ _ → [])) n
                    
  enumerate-wb₂ {d'} (d₁ `∪ d₂) n
    with enumerate-wb₂ {d'} d₁ n | enumerate-wb₂ {d'} d₂ n 
  ... | r₁ | r₂ = cong₂ (λ xs ys → (map inj₁ xs ++ []) ++ map inj₂ ys ++ []) r₁ r₂

  enumerate-wb₂ {d'} (d₁ `× d₂) n
    with enumerate-wb₂ {d'} d₁ n | enumerate-wb₂ {d'} d₂ n
  ... | r₁ | r₂ = cong₂ (λ xs ys → concatMap (λ f → map f ys)
                        (concatMap (λ f → map f xs) [ _,_ ])) r₁ r₂

  enumerate-wb₂ `var       n = refl
  enumerate-wb₂ `1         n = refl
  enumerate-wb₂ `0         n = refl
  enumerate-wb₂ (`k S)     n = refl


  -----------------------------------------------------------------------------------------------------------------
  -- all recursive calls in enumerators produced by `enumerate` use one step of fuel  

  ≤suc : ∀ n → n ≤ suc n
  ≤suc zero    = z≤n
  ≤suc (suc n) = s≤s (≤suc n)

  fix-step : ∀ {d x n} → x ∈ enumerate {d' = enums d} (enums d) (fix (λ _ → enumerate (enums d))) n
                       → x ∈ fix (λ _ → enumerate {enums d} (enums d)) tt (suc n)
  fix-step {d} {v} {n} el = enumerate-wb₁ n n (suc n) d d v (∈-resp-≡ (enumerate-wb₂ (enums d) n) el) (≤suc _)


  -----------------------------------------------------------------------------------------------------------------
  -- Completeness theorem for `enumerate`

  complete : {d' : Desc k-info} (d : Desc k-info) →
             Complete (        enumerate {enums d'} (enums d ))
                      (const $ enumerate {enums d'} (enums d')) 

  loc  (complete (d₁ `∪ d₂) {inj₁ x}) = loc (complete d₁ {x})
  loc  (complete (d₁ `∪ d₂) {inj₂ y}) = loc (complete d₂ {y})
  elem (complete (d₁ `∪ d₂) {inj₁ x}) = ∈-++⁺ˡ (∈-++⁺ˡ (∈-map⁺ inj₁ (elem (complete d₁ {x}))))
  elem (complete (d₁ `∪ d₂) {inj₂ y}) = ∈-++⁺ʳ ((‼ inj₁ ⊛ enumerate (enums d₁)) _ _)
                                               (∈-++⁺ˡ (∈-map⁺ inj₂ (elem (complete d₂ {y}))))
  
  loc  (complete (d₁ `× d₂) {x , y}) = max (loc (complete d₁ {x})) (loc (complete d₂ {y}))
  elem (complete (d₁ `× d₂) {x , y}) = prod-elem (enumerate (enums d₁))
                                                 (enumerate (enums d₂))
                                                 (monotone d₁ _ _ _ x (elem (complete d₁ {x})) (n≤maxnm _ _))
                                                 (monotone d₂ _ _ _ y (elem (complete d₂ {y})) (m≤maxnm _ _))

  loc  (complete {d'} `var {⟨ x ⟩}) = suc (loc (complete d' {x}))
  elem (complete {d'} `var {⟨ x ⟩}) with fix-step {d'} (elem (complete d' {x}))
  ... | p = ∈-++⁺ˡ {ys = []} (∈-map⁺ ⟨_⟩ p)

  loc  (complete `1) = 0
  elem (complete `1) = here refl
  
  complete (`k S {ki}) {x} = k-complete ki


  -----------------------------------------------------------------------------------------------------------------
  -- Completeness theorem or `enumerate-μ`

  iscomplete : (d' : Desc k-info) → IsComplete (enumerate-μ {enums d'} (enums d'))
  loc  (iscomplete d' {tt} {⟨ x ⟩}) = loc (complete {d'} d' {x})
  elem (iscomplete d' {tt} {⟨ x ⟩}) = ∈-map⁺ ⟨_⟩ (elem (complete d'))
