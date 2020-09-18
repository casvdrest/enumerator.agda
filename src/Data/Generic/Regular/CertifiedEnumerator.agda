{-# OPTIONS --safe #-}

module Data.Generic.Regular.CertifiedEnumerator where

open import Data.Enumerate
open import Data.Generic.Regular.Universe
open import Data.Generic.Regular.Enumerator

open import Data.Generic.Regular.Properties.Monotone
open import Data.Generic.Regular.Properties.Complete

module _ where 

  cenumerate : (D : Desc CEnumerator) → CEnumerator (μ (enums D))
  enum (cenumerate D) = enumerate (enums D)
  mono (cenumerate D) = monotone D
  comp (cenumerate D) = complete D
