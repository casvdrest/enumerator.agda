{-# OPTIONS --safe #-}

module Instances.Nat where

open import Data.List

open import Data.Nat
open import Data.Enumerate

module _ where

  nats : Enumerator ℕ
  nats zero    = []
  nats (suc n) = (‼ zero ⟨∣⟩ μ) n
    where  μ : Enumerator ℕ
           μ _ = nats n
