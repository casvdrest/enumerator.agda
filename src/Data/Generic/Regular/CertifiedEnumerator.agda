{-# OPTIONS --safe #-}

module Data.Generic.Regular.CertifiedEnumerator where

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit 
open import Data.Enumerate
open import Data.List
open import Data.Nat

open import Data.Generic.Regular.Universe
open import Data.Generic.Regular.Enumerator

open import Data.Generic.Regular.Properties.Monotone
open import Data.Generic.Regular.Properties.Complete

open import Relation.Binary.PropositionalEquality using (refl ; cong ; _≡_)

open import Function using (const ; Inverse ; id ; _$_)

module _ where 

  cenumerate : (D : Desc CEnumerator) → CEnumerator (μ (enums D))
  enum (cenumerate D) = enumerate (enums D)
  mono (cenumerate D) = monotone D
  comp (cenumerate D) = complete D
