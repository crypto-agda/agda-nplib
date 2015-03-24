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

  open From-Op₂ _∙_ public renaming (op= to ∙=)
  open From-Monoid-Ops ε _∙_ public

record Monoid-Struct {ℓ} {M : Type ℓ} (mon-ops : Monoid-Ops M) : Type ℓ where
  constructor _,_
  open Monoid-Ops mon-ops

  -- laws
  field
    assocs   : Associative _∙_ × Associative (flip _∙_)
    identity : Identity  ε _∙_

  ε∙-identity : LeftIdentity ε _∙_
  ε∙-identity = fst identity

  ∙ε-identity : RightIdentity ε _∙_
  ∙ε-identity = snd identity

  assoc  = fst assocs
  !assoc = snd assocs

  open From-Assoc assoc public hiding (assocs)
  open From-Assoc-LeftIdentity  assoc ε∙-identity public
  open From-Assoc-RightIdentity assoc ∙ε-identity public

record Monoid {ℓ}(M : Type ℓ) : Type ℓ where
  constructor _,_
  field
    mon-ops    : Monoid-Ops M
    mon-struct : Monoid-Struct mon-ops
  open Monoid-Ops    mon-ops    public
  open Monoid-Struct mon-struct public

-- A renaming of Monoid-Ops with additive notation
module Additive-Monoid-Ops {ℓ}{M : Set ℓ} (mon : Monoid-Ops M) where
  private
   module M = Monoid-Ops mon
    using    ()
    renaming ( _∙_ to _+_
             ; ε to `0
             ; _² to 2⊗_
             ; _³ to 3⊗_
             ; _⁴ to 4⊗_
             ; _^¹⁺_ to _⊗¹⁺_
             ; _^⁺_ to _⊗⁺_
             ; ∙= to +=
             )
  open M public using (`0; +=)
  infixl 6 _+_
  infixl 7 _⊗¹⁺_ _⊗⁺_ 2⊗_ 3⊗_ 4⊗_
  _+_   = M._+_
  _⊗¹⁺_ = M._⊗¹⁺_
  _⊗⁺_  = M._⊗⁺_
  2⊗_   = M.2⊗_
  3⊗_   = M.3⊗_
  4⊗_   = M.4⊗_

-- A renaming of Monoid-Struct with additive notation
module Additive-Monoid-Struct {ℓ}{M : Type ℓ}{mon-ops : Monoid-Ops M}
                              (mon-struct : Monoid-Struct mon-ops)
  = Monoid-Struct mon-struct
    renaming ( identity to +-identity
             ; ε∙-identity to 0+-identity
             ; ∙ε-identity to +0-identity
             ; assocs to +-assocs
             ; assoc to +-assoc
             ; !assoc to +-!assoc
             ; assoc= to +-assoc=
             ; !assoc= to +-!assoc=
             ; inner= to +-inner=
             )

-- A renaming of Monoid with additive notation
module Additive-Monoid {ℓ}{M : Type ℓ} (mon : Monoid M) where
  open Additive-Monoid-Ops    (Monoid.mon-ops    mon) public
  open Additive-Monoid-Struct (Monoid.mon-struct mon) public

-- A renaming of Monoid-Ops with multiplicative notation
module Multiplicative-Monoid-Ops {ℓ}{M : Type ℓ} (mon-ops : Monoid-Ops M)
  = Monoid-Ops mon-ops
    renaming ( _∙_ to _*_
             ; ε to `1
             ; ∙= to *=
             )

-- A renaming of Monoid-Struct with multiplicative notation
module Multiplicative-Monoid-Struct {ℓ}{M : Type ℓ}{mon-ops : Monoid-Ops M}
                                    (mon-struct : Monoid-Struct mon-ops)
  = Monoid-Struct mon-struct
    renaming ( identity to *-identity
             ; ε∙-identity to 1*-identity
             ; ∙ε-identity to *1-identity
             ; assocs to *-assocs
             ; assoc to *-assoc
             ; !assoc to *-!assoc
             ; assoc= to *-assoc=
             ; !assoc= to *-!assoc=
             ; inner= to *-inner=
             )

-- A renaming of Monoid with multiplicative notation
module Multiplicative-Monoid {ℓ}{M : Type ℓ} (mon : Monoid M) where
  open Multiplicative-Monoid-Ops    (Monoid.mon-ops    mon) public
  open Multiplicative-Monoid-Struct (Monoid.mon-struct mon) public

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
  from-assoc = From-Op₂.From-Assoc.assocs _∙_ assoc

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
  ×-mon-ops    = zip _+_ _*_ , `0 , `1

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
