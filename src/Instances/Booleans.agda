{-# OPTIONS --safe #-}

module Instances.Booleans where

open import Data.Enumerate
open import Data.Bool
open import Data.Empty

open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

open import Relation.Binary.PropositionalEquality


module _ where

  bools : Enumerator Bool
  bools = ‼ false ⟨∣⟩ ‼ true
  
  boolsWrong : Enumerator Bool
  boolsWrong = ∅

  bools-complete : Complete bools
  bools-complete {false} = ↑l 0 (here refl)
  bools-complete {true}  = ↑l 0 (there (here refl))

  boolsWrong-incomplete : Complete boolsWrong → ⊥ 
  boolsWrong-incomplete x with x {false}
  ... | ()
