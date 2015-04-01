{-# OPTIONS --without-K #-}
open import Type using (Type_)
open import Function.NP
open import Function.Extensionality
open import Data.Product.NP
open import Relation.Binary.PropositionalEquality.NP using (_≡_; idp; ap; ap₂)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Algebra.Raw

module Algebra.Monoid where

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

  open From-Monoid-Ops mon-ops
  open From-Assoc               assoc             public hiding (assocs)
  open From-Identities          identity          public
  open From-Assoc-LeftIdentity  assoc ε∙-identity public
  open From-Assoc-RightIdentity assoc ∙ε-identity public

record Monoid {ℓ}(M : Type ℓ) : Type ℓ where
  constructor _,_
  field
    mon-ops    : Monoid-Ops M
    mon-struct : Monoid-Struct mon-ops
  open Monoid-Ops    mon-ops    public
  open Monoid-Struct mon-struct public

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
             ; ε^⁺ to 0⊗⁺
             )

-- A renaming of Monoid with additive notation
module Additive-Monoid {ℓ}{M : Type ℓ} (mon : Monoid M) where
  open Additive-Monoid-Ops    (Monoid.mon-ops    mon) public
  open Additive-Monoid-Struct (Monoid.mon-struct mon) public

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
             ; ε^⁺ to 1^⁺
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

-- The monoidal structure of endomorphisms
module _ {a}(A : Type a) where
  ∘-mon-ops : Monoid-Ops (Endo A)
  ∘-mon-ops = _∘′_ , id

  ∘-mon-struct : Monoid-Struct ∘-mon-ops
  ∘-mon-struct = (idp , idp) , (idp , idp)

  ∘-mon : Monoid (Endo A)
  ∘-mon = ∘-mon-ops , ∘-mon-struct

module Product {a}{A : Type a}{b}{B : Type b}
               (𝔸 : Monoid A)(𝔹 : Monoid B) where
  open Additive-Monoid 𝔸
  open Multiplicative-Monoid 𝔹

  ×-mon-ops    : Monoid-Ops (A × B)
  ×-mon-ops    = zip _+_ _*_ , 0# , 1#

  ×-mon-struct : Monoid-Struct ×-mon-ops
  ×-mon-struct = (ap₂ _,_ +-assoc *-assoc , ap₂ _,_ +-!assoc *-!assoc)
               , ap₂ _,_ (fst +-identity) (fst *-identity)
               , ap₂ _,_ (snd +-identity) (snd *-identity)

  ×-mon : Monoid (A × B)
  ×-mon = ×-mon-ops , ×-mon-struct

  open Monoid ×-mon public

{-
This module shows how properties of a monoid 𝕄 are carried on
functions from any type A to 𝕄.
However since the function type can be dependent, this also generalises
the product of monoids (since Π 𝟚 [ A , B ] ≃ A × B).
-}
module Pointwise {{_ : FunExt}}{a}(A : Type a){m}{M : A → Type m}
                 (𝕄 : (x : A) → Monoid (M x)) where
  private
    module 𝕄 {x} = Monoid (𝕄 x)
  open 𝕄 hiding (mon-ops; mon-struct)

  ⟨ε⟩ : Π A M
  ⟨ε⟩ = λ _ → ε

  _⟨∙⟩_ : Op₂ (Π A M)
  (f ⟨∙⟩ g) x = f x ∙ g x

  mon-ops : Monoid-Ops (Π A M)
  mon-ops = _⟨∙⟩_ , ⟨ε⟩

  mon-struct : Monoid-Struct mon-ops
  mon-struct = (λ=ⁱ assoc , λ=ⁱ !assoc) , λ=ⁱ ε∙-identity , λ=ⁱ ∙ε-identity

  mon : Monoid (Π A M)
  mon = mon-ops , mon-struct

  open Monoid mon public hiding (mon-ops; mon-struct)

-- Non-dependent version of Pointwise′
module Pointwise′ {{_ : FunExt}}{a}(A : Type a){m}{M : Type m}(𝕄 : Monoid M) =
  Pointwise A (λ _ → 𝕄)
  {- OR
  open Monoid 𝕄 hiding (mon-ops; mon-struct)

  ⟨ε⟩ : A → M
  ⟨ε⟩ = λ _ → ε

  _⟨∙⟩_ : Op₂ (A → M)
  (f ⟨∙⟩ g) x = f x ∙ g x

  mon-ops : Monoid-Ops (A → M)
  mon-ops = _⟨∙⟩_ , ⟨ε⟩

  mon-struct : Monoid-Struct mon-ops
  mon-struct = (λ=ⁱ assoc , λ=ⁱ !assoc) , λ=ⁱ ε∙-identity , λ=ⁱ ∙ε-identity

  mon : Monoid (A → M)
  mon = mon-ops , mon-struct

  open Monoid mon public hiding (mon-ops; mon-struct)
  -}
-- -}
-- -}
-- -}
-- -}
