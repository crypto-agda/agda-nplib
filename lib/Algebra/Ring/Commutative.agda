{-# OPTIONS --without-K #-}
open import Relation.Binary.PropositionalEquality.NP
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Data.Product.NP using (fst ; snd)
open import Algebra.Raw
open import Algebra.Monoid
open import Algebra.Monoid.Commutative
open import Algebra.Group
open import Algebra.Group.Abelian
open import Algebra.Ring

module Algebra.Ring.Commutative where

record Commutative-Ring-Struct {ℓ} {A : Set ℓ} (rng-ops : Ring-Ops A) : Set ℓ where
  open Ring-Ops rng-ops

  open ≡-Reasoning

  field
    +-abelian-grp-struct : Abelian-Group-Struct +-grp-ops
    *-comm-mon-struct    : Commutative-Monoid-Struct *-mon-ops
    *-+-distrs           : _*_ DistributesOver _+_

  open Additive-Abelian-Group-Struct +-abelian-grp-struct public
  -- 0−-involutive   : Involutive 0−_
  -- cancels-+-left  : LeftCancel _+_
  -- cancels-+-right : RightCancel _+_
  -- ...

  open Multiplicative-Commutative-Monoid-Struct *-comm-mon-struct public

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

  *-mon-struct : Monoid-Struct *-mon-ops
  *-mon-struct = Commutative-Monoid-Struct.mon-struct *-comm-mon-struct

  *-comm-mon : Commutative-Monoid A
  *-comm-mon = *-mon-ops , *-comm-mon-struct

  *-mon : Monoid A
  *-mon = *-mon-ops , *-mon-struct

  module *-Mon = Commutative-Monoid *-comm-mon

  rng-struct : Ring-Struct rng-ops
  rng-struct = record
                 { +-abelian-grp-struct = +-abelian-grp-struct
                 ; *-mon-struct = *-mon-struct
                 ; *-+-distrs = *-+-distrs }

  ring : Ring A
  ring = rng-ops , rng-struct

  module +*-Ring = Ring ring

  *-+-distr : _*_ DistributesOverˡ _+_
  *-+-distr = fst *-+-distrs

  ²-+-distr : ∀ {x y} → (x + y)² ≡ x ² + y ² + 2* x * y
  ²-+-distr {x} {y} = (x + y)²
                    ≡⟨ *-+-distrˡ ⟩
                      (x + y) * x + (x + y) * y
                    ≡⟨ += *-+-distrʳ *-+-distrʳ ⟩
                      x ² + y * x + (x * y + y ²)
                    ≡⟨ += (+= idp *-comm) +-comm ∙ +-interchange ⟩
                      x ² + y ² + 2*(x * y)
                    ≡⟨ += idp 2*-*-distr ⟩
                       x ² + y ² + 2* x * y
                    ∎

  ²-*-distr : ∀ {x y} → (x * y)² ≡ x ² * y ²
  ²-*-distr = *-interchange

  ²-−-distr : ∀ {x y} → (x − y)² ≡ x ² + y ² − 2* x * y
  ²-−-distr = ²-+-distr ∙ += (+= idp ²-0−-distr) (*-comm ∙ ! 0−-*-distr ∙ 0−= *-comm)

record Commutative-Ring {ℓ} (A : Set ℓ) : Set ℓ where
  constructor _,_
  field
    rng-ops         : Ring-Ops A
    comm-rng-struct : Commutative-Ring-Struct rng-ops
  open Ring-Ops                rng-ops         public
  open Commutative-Ring-Struct comm-rng-struct public
