{-# OPTIONS --safe #-}

module Data.Generic.Indexed.CertifiedEnumerator where

open import Data.Enumerate
open import Data.Generic.Indexed.Universe
open import Data.Generic.Indexed.Enumerator

open import Data.Generic.Indexed.Properties.Monotone
open import Data.Generic.Indexed.Properties.Complete

open import Function using (const ; Inverse ; id ; _$_ ; _∘_)

module _ where 

  cenumerate : (φ : Func CEnumerator I) (i : I) → CEnumerator (μ (mk (enums ∘ out φ)) i)
  enum (cenumerate φ i) = enumerate (mk (enums ∘ out φ)) i
  mono (cenumerate φ i) = monotone φ i
  comp (cenumerate φ i) = complete φ i
