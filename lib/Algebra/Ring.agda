{-# OPTIONS --without-K #-}
open import Relation.Binary.PropositionalEquality.NP
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Data.Product.NP using (fst; snd)
open import Algebra.Raw
open import Algebra.Monoid
open import Algebra.Group
open import Algebra.Group.Abelian

module Algebra.Ring where

record Ring-Struct {ℓ} {A : Set ℓ} (rng-ops : Ring-Ops A) : Set ℓ where
  inductive -- NO_ETA
  open Ring-Ops rng-ops

  open ≡-Reasoning

  field
    +-abelian-grp-struct : Abelian-Group-Struct +-grp-ops
    *-mon-struct         : Monoid-Struct *-mon-ops
    *-+-distrs           : _*_ DistributesOver _+_

  open Additive-Abelian-Group-Struct +-abelian-grp-struct public
  -- 0−-involutive   : Involutive 0−_
  -- cancels-+-left  : LeftCancel _+_
  -- cancels-+-right : RightCancel _+_
  -- ...

  open Multiplicative-Monoid-Struct *-mon-struct public

  -- open From-Field-Ops field-ops
  open From-Ring-Ops rng-ops
  open From-+Group-*Identity-DistributesOver
             +-assoc
             0+-identity
             +0-identity
             (snd 0−-inverse)
             1*-identity
             *1-identity
             *-+-distrs
             public
             hiding (+-comm)

  +-grp-struct : Group-Struct +-grp-ops
  +-grp-struct = Abelian-Group-Struct.grp-struct +-abelian-grp-struct

  +-abelian-grp : Abelian-Group A
  +-abelian-grp = +-grp-ops , +-abelian-grp-struct

  +-grp : Group A
  +-grp = +-grp-ops , +-grp-struct

  -- Since the Abelian-Group module includes all what Group and
  -- Monoid provide, we can expose a single module.
  module +-Grp = Abelian-Group +-abelian-grp

  *-mon : Monoid A
  *-mon = *-mon-ops , *-mon-struct

  module *-Mon = Monoid *-mon

record Ring {ℓ} (A : Set ℓ) : Set ℓ where
  inductive -- NO_ETA
  constructor _,_
  field
    rng-ops    : Ring-Ops A
    rng-struct : Ring-Struct rng-ops
  open Ring-Ops    rng-ops    public
  open Ring-Struct rng-struct public
-- -}
