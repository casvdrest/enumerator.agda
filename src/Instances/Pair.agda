{-# OPTIONS --safe #-}

module Instances.Pair where

open import Data.Product
open import Data.Enumerate

module _ where

  pairs : Enumerator A → Enumerator B → Enumerator (A × B)
  pairs e₁ e₂ = ‼ _,_ ⊛ e₁ ⊛ e₂
