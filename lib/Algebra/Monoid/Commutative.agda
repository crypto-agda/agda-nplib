{-# OPTIONS --without-K #-}
open import Type using () renaming (Type_ to Type)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Algebra.Monoid
open import Algebra.Raw

module Algebra.Monoid.Commutative where

record Commutative-Monoid-Struct {ℓ} {M : Type ℓ} (mon-ops : Monoid-Ops M) : Type ℓ where
  inductive -- NO_ETA
  constructor _,_
  open Monoid-Ops mon-ops
  open From-Monoid-Ops mon-ops
  field
    mon-struct : Monoid-Struct mon-ops
    comm : Commutative _∙_
  open Monoid-Struct mon-struct public
  open From-Assoc-Comm assoc comm public
    hiding (!assoc=; assoc=; inner=; assocs)

record Commutative-Monoid {ℓ}(M : Type ℓ) : Type ℓ where
  inductive -- NO_ETA
  constructor _,_
  field
    mon-ops    : Monoid-Ops M
    mon-comm   : Commutative-Monoid-Struct mon-ops
  open Monoid-Ops    mon-ops    public
  open Commutative-Monoid-Struct mon-comm public
  mon : Monoid M
  mon = record { mon-struct = mon-struct }

module Additive-Commutative-Monoid-Struct
         {ℓ}{M : Type ℓ}{mon-ops : Monoid-Ops M}
         (comm-mon-struct : Commutative-Monoid-Struct mon-ops) where
  open Additive-Monoid-Struct (Commutative-Monoid-Struct.mon-struct comm-mon-struct) public
  open Commutative-Monoid-Struct comm-mon-struct
    public
    using    ()
    renaming ( comm to +-comm
             ; comm= to +-comm=
             ; assoc-comm to +-assoc-comm
             ; !assoc-comm to +-!assoc-comm
             ; interchange to +-interchange
             ; outer= to +-outer=
             ; on-sides to +-on-sides
             ; ²-∙-distr to 2*-+-distr
             ; ²-∙-distr' to 2*-+-distr'
             )

module Additive-Commutative-Monoid {ℓ}{M : Type ℓ}(mon : Commutative-Monoid M) where
  open Additive-Monoid-Ops                (Commutative-Monoid.mon-ops  mon) public
  open Additive-Commutative-Monoid-Struct (Commutative-Monoid.mon-comm mon) public

module Multiplicative-Commutative-Monoid-Struct
         {ℓ}{M : Type ℓ}{mon-ops : Monoid-Ops M}
         (comm-mon-struct : Commutative-Monoid-Struct mon-ops) where
  open Multiplicative-Monoid-Struct (Commutative-Monoid-Struct.mon-struct comm-mon-struct) public
  open Commutative-Monoid-Struct comm-mon-struct
    public
    using    ()
    renaming ( comm to *-comm
             ; comm= to *-comm=
             ; assoc-comm to *-assoc-comm
             ; !assoc-comm to *-!assoc-comm
             ; interchange to *-interchange
             ; outer= to *-outer=
             ; on-sides to *-on-sides
             ; ²-∙-distr to ²-*-distr
             ; ²-∙-distr' to ²-*-distr'
             )

module Multiplicative-Commutative-Monoid {ℓ}{M : Type ℓ}(mon : Commutative-Monoid M) where
  open Multiplicative-Monoid-Ops                (Commutative-Monoid.mon-ops  mon) public
  open Multiplicative-Commutative-Monoid-Struct (Commutative-Monoid.mon-comm mon) public
-- -}
-- -}
-- -}
-- -}
