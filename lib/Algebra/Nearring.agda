{-# OPTIONS --without-K #-}
open import Relation.Binary.PropositionalEquality.NP
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Function.Extensionality
open import Data.Product.NP
open import Data.Nat.NP using (ℕ; zero; fold) renaming (suc to 1+)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Algebra.Raw
open import Algebra.Monoid
open import Algebra.Monoid.Commutative
open import Algebra.Group
open import Algebra.Group.Abelian
open import HoTT

module Algebra.Nearring where

record Nearring+1-Struct {ℓ} {A : Set ℓ} (rng-ops : Ring-Ops A) : Set ℓ where
  open Ring-Ops rng-ops

  open ≡-Reasoning

  field
    +-grp-struct : Group-Struct +-grp-ops
    *-mon-struct : Monoid-Struct *-mon-ops
    *-+-distrʳ   : _*_ DistributesOverʳ _+_

  open Additive-Group-Struct +-grp-struct public
  -- 0−-involutive   : Involutive 0−_
  -- cancels-+-left  : LeftCancel _+_
  -- cancels-+-right : RightCancel _+_
  -- ...

  open Multiplicative-Monoid-Struct *-mon-struct public

  open From-Ring-Ops rng-ops
  open From-+Group-1*Identity-DistributesOverʳ
             +-assoc
             0+-identity
             +0-identity
             (snd 0−-inverse)
             1*-identity
             *-+-distrʳ
             public

  +-grp : Group A
  +-grp = +-grp-ops , +-grp-struct

  module +-Grp = Group +-grp

  *-mon : Monoid A
  *-mon = *-mon-ops , *-mon-struct

  module *-Mon = Monoid *-mon

record Nearring+1 {ℓ} (A : Set ℓ) : Set ℓ where
  field
    rng-ops           : Ring-Ops A
    nearring+1-struct : Nearring+1-Struct rng-ops
  open Ring-Ops          rng-ops           public
  open Nearring+1-Struct nearring+1-struct public
-- -}
-- -}
-- -}
-- -}
-- -}
