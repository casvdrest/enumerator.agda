module Testing where

open import Data.Enumerate

open import Data.Bool renaming (_≟_ to _≟b_)
open import Data.Nat
open import Data.Product

open import Instances.Expr

open import Function

module _ where

  open import Data.List hiding (and)
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality 

  Property : Set₁
  Property = Set

  data Result (A : Set) : Set where
    success        : Result A
    counterexample : A → Result A

  test : (prop : A → Property) → ((x : A) → Dec (prop x)) → List A → Result A
  test _ dec [] = success
  test _ dec (x ∷ xs) with dec x
  ... | yes p = test _ dec xs
  ... | no  _ = counterexample x

module _ where

  open import Data.List hiding (and)
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality 

  and-left-identity : Expr 𝕓 → Property
  and-left-identity e = eval (and (bool true) e) ≡ eval e 

  dec₁ : (e : Expr 𝕓) → Dec (and-left-identity e)
  dec₁ e = eval (and (bool true) e) ≟b eval e

  -- Use Agsy to find counterexample
  runtest₁ : test and-left-identity dec₁ (enum (exprs 𝕓) 2) ≡ counterexample {!!}
  runtest₁ = refl
  
  -- Can't give `refl` because property can be falsified
  runtest₂ : test and-left-identity dec₁ (enum (exprs 𝕓) 2) ≡ success
  runtest₂ = {!!}

module _ where

  open import Data.List hiding (and)
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality 

  open import Instances.Pair

  add-commutative : Expr 𝕟 → Expr 𝕟 → Property
  add-commutative e₁ e₂ = eval (add e₁ e₂) ≡ eval (add e₂ e₁)

  dec₂ : (e₁ e₂ : Expr 𝕟) → Dec (add-commutative e₁ e₂) 
  dec₂ e₁ e₂ = eval (add e₁ e₂) ≟ eval (add e₂ e₁)

  runtest₃ : test (uncurry $ add-commutative) (uncurry $ dec₂) (pairs (enum (exprs 𝕟)) (enum (exprs 𝕟)) 3) ≡ success
  runtest₃ = refl
