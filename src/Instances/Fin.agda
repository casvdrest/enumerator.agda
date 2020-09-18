{-# OPTIONS --safe #-}

module Instances.Fin where

open import Data.Fin
open import Data.Nat
open import Data.Enumerate

module _ where

  fins : (n : ℕ) → Enumerator (Fin n)
  fins zero     = ∅
  fins (suc n)  = ‼ zero ⟨∣⟩ (‼ suc ⊛ fins n)


