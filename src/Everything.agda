{-# OPTIONS --safe #-}

module Everything where

------------------------------
-- Section 1 (Introduction) --
------------------------------

-- `Expr` data type
open import Instances.Expr


-----------------------------------------
-- Section 2 (Enumerator construction) --
-----------------------------------------

-- Enumerator type + combinators + correctness properties (2.1)
open import Data.Enumerate

-- 2.1 examples
open import Instances.Nat 
open import Instances.Fin
open import Instances.Pair
open import Instances.Booleans


-------------------------------
-- Section 3 (Regular Types) --
-------------------------------

-- Universe definition
open import Data.Generic.Regular.Universe
-- Generic enumerator
open import Data.Generic.Regular.Enumerator
-- Enuemrators respect isomorphism
open import Data.Enumerate.Properties
-- Correctness proofs
open import Data.Generic.Regular.Properties.Monotone
open import Data.Generic.Regular.Properties.Complete
-- Certified enumerator
open import Data.Generic.Regular.CertifiedEnumerator


-------------------------------
-- Section 4 (Indexed Types) --
-------------------------------

-- Universe definition
open import Data.Generic.Indexed.Universe
-- Generic enumerator
open import Data.Generic.Indexed.Enumerator
-- Correctness proofs
open import Data.Generic.Indexed.Properties.Monotone
open import Data.Generic.Indexed.Properties.Complete
-- Certified enumerator
open import Data.Generic.Indexed.CertifiedEnumerator


----------------------
-- Section 5 (STLC) --
----------------------

-- Types
open import Instances.Type
-- Membership
open import Instances.Membership
-- Terms
open import Instances.STLC

