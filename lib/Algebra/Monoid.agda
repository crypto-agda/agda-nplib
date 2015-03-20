{-# OPTIONS --without-K #-}
open import Type using () renaming (Type_ to Type)
open import Level.NP
open import Function.NP
open import Data.Product.NP
open import Data.Nat
  using    (ℕ; zero)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; suc to 1+_)
import Data.Nat.Properties.Simple as ℕ°
open import Data.Integer.NP
  using    (ℤ; +_; -[1+_]; _⊖_; -_; module ℤ°)
  renaming ( _+_ to _+ℤ_; _-_ to _−ℤ_; _*_ to _*ℤ_
           ; suc to sucℤ; pred to predℤ
           )
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open ≡-Reasoning

module Algebra.Monoid where

record Monoid-Ops {ℓ} (M : Type ℓ) : Type ℓ where
  constructor _,_
  infixl 7 _∙_

  field
    _∙_ : M → M → M
    ε   : M

  open FromOp₂ _∙_ public renaming (op= to ∙=)
  open FromMonoidOps ε _∙_ public

record Monoid-Struct {ℓ} {M : Type ℓ} (mon-ops : Monoid-Ops M) : Type ℓ where
  constructor _,_
  open Monoid-Ops mon-ops

  -- laws
  field
    assocs   : Associative _∙_ × Associative (flip _∙_)
    identity : Identity  ε _∙_

  idl : LeftIdentity ε _∙_
  idl = fst identity

  idr : RightIdentity ε _∙_
  idr = snd identity

  assoc = fst assocs
  !assoc = snd assocs

  open FromAssoc assoc public hiding (assocs)
  open FromLeftIdentityAssoc  idl assoc public
  open FromRightIdentityAssoc idr assoc public

record Monoid {ℓ}(M : Type ℓ) : Type ℓ where
  constructor _,_
  field
    mon-ops    : Monoid-Ops M
    mon-struct : Monoid-Struct mon-ops
  open Monoid-Ops    mon-ops    public
  open Monoid-Struct mon-struct public

record Commutative-Monoid-Struct {ℓ} {M : Type ℓ} (mon-ops : Monoid-Ops M) : Type ℓ where
  constructor _,_
  open Monoid-Ops mon-ops
  field
    mon-struct : Monoid-Struct mon-ops
    comm : Commutative _∙_
  open Monoid-Struct mon-struct public
  open FromAssocComm assoc comm public
    hiding (!assoc=; assoc=; inner=; assocs)

record Commutative-Monoid {ℓ}(M : Type ℓ) : Type ℓ where
  constructor _,_
  field
    mon-ops    : Monoid-Ops M
    mon-comm   : Commutative-Monoid-Struct mon-ops
  open Monoid-Ops    mon-ops    public
  open Commutative-Monoid-Struct mon-comm public
  mon : Monoid M
  mon = record { mon-struct = mon-struct }

-- A renaming of Monoid with additive notation
module Additive-Monoid {ℓ}{M : Type ℓ} (mon : Monoid M) = Monoid mon
    renaming ( _∙_ to _+_; ε to 0ᵐ
             ; assoc to +-assoc; identity to +-identity
             ; !assoc to +-!assoc
             ; ∙= to +=
             ; _^⁺_ to _⊗⁺_
             )

-- A renaming of Monoid with multiplicative notation
module Multiplicative-Monoid {ℓ}{M : Type ℓ} (mon : Monoid M) = Monoid mon
    renaming ( _∙_ to _*_; ε to 1ᵐ
             ; assoc to *-assoc; identity to *-identity
             ; !assoc to *-!assoc
             ; ∙= to *=
             )

module Additive-Commutative-Monoid {ℓ}{M : Type ℓ} (mon-comm : Commutative-Monoid M)
  = Commutative-Monoid mon-comm
    renaming ( _∙_ to _+_; ε to 0ᵐ
             ; assoc to +-assoc; identity to +-identity
             ; !assoc to +-!assoc
             ; ∙= to +=
             ; assoc= to +-assoc=
             ; !assoc= to +-!assoc=
             ; inner= to +-inner=
             ; assoc-comm to +-assoc-comm
             ; interchange to +-interchange
             ; outer= to +-outer=
             )

module Multiplicative-Commutative-Monoid
     {ℓ}{M : Type ℓ} (mon : Commutative-Monoid M) = Commutative-Monoid mon
    renaming ( _∙_ to _*_; ε to 1ᵐ
             ; assoc to *-assoc; identity to *-identity
             ; !assoc to *-!assoc
             ; ∙= to *=
             ; assoc= to *-assoc=
             ; !assoc= to *-!assoc=
             ; inner= to *-inner=
             ; assoc-comm to *-assoc-comm
             ; interchange to *-interchange
             ; outer= to *-outer=
             )

module Monoidᵒᵖ {ℓ}{M : Type ℓ} where
  _ᵒᵖ-ops : Monoid-Ops M → Monoid-Ops M
  (_∙_ , ε) ᵒᵖ-ops = flip _∙_ , ε

  _ᵒᵖ-struct : {mon : Monoid-Ops M} → Monoid-Struct mon → Monoid-Struct (mon ᵒᵖ-ops)
  (assocs , identities) ᵒᵖ-struct = (swap assocs , swap identities)

  _ᵒᵖ : Monoid M → Monoid M
  (ops , struct)ᵒᵖ = _ , struct ᵒᵖ-struct

  ᵒᵖ∘ᵒᵖ-id : ∀ {mon} → (mon ᵒᵖ) ᵒᵖ ≡ mon
  ᵒᵖ∘ᵒᵖ-id = idp

module _ {a}{A : Type a}(_∙_ : Op₂ A)(assoc : Associative _∙_) where
  from-assoc = FromOp₂.FromAssoc.assocs _∙_ assoc

--import Data.Vec.NP as V
{-
module _ {A B : Type} where
  (f : Vec  : Vec M n) → f ⊛ x (∀ i → )

module VecMonoid {M : Type} (mon : Monoid M) where
  open V
  open Monoid mon

  module _ n where
    ×-mon-ops : Monoid-Ops (Vec M n)
    ×-mon-ops = zipWith _∙_ , replicate ε

    ×-mon-struct : Monoid-Struct ×-mon-ops
    ×-mon-struct = (λ {x}{y}{z} → {!replicate ? ⊛ ?!}) , {!!} , {!!}
-}

module MonoidProduct {a}{A : Type a}{b}{B : Type b}
                     (monA0+ : Monoid A)(monB1* : Monoid B) where
  open Additive-Monoid monA0+
  open Multiplicative-Monoid monB1*

  ×-mon-ops    : Monoid-Ops (A × B)
  ×-mon-ops    = zip _+_ _*_ , 0ᵐ , 1ᵐ

  ×-mon-struct : Monoid-Struct ×-mon-ops
  ×-mon-struct = (ap₂ _,_ +-assoc *-assoc , ap₂ _,_ +-!assoc *-!assoc)
               , ap₂ _,_ (fst +-identity) (fst *-identity)
               , ap₂ _,_ (snd +-identity) (snd *-identity)

  ×-mon : Monoid (A × B)
  ×-mon = ×-mon-ops , ×-mon-struct

  open Monoid ×-mon public
-- -}
-- -}
-- -}
-- -}
