module Instances.Types where

open import Data.Enumerate
open import Data.List
open import Data.Nat
open import Data.Product

module _ where

  nats : Enumerator ℕ
  nats zero    = []
  nats (suc n) = (‼ zero ⟨∣⟩ (‼ suc ⊛ λ _ → nats n)) n
    where μ = nats n

  pairs : {A B : Set} → Enumerator A → Enumerator B → Enumerator (A × B)
  pairs e₁ e₂  = ‼ _,_ ⊛ e₁ ⊛ e₂
