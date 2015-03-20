module Data.Integer.NP where

open import Data.Integer public
open import Data.Integer.Properties
open import Relation.Binary
import Algebra
import Relation.Binary.PropositionalEquality as ≡

ℤˢ = ≡.setoid ℤ

module ℤ≤   = DecTotalOrder decTotalOrder
module ℤ°   = Algebra.CommutativeRing commutativeRing
module ℤ+   = Algebra.CommutativeMonoid ℤ°.+-commutativeMonoid
module ℤ+′  = Algebra.Monoid ℤ°.+-monoid
module ℤˢ   = Setoid ℤˢ

-- module ℤcmp = StrictTotalOrder TODO
