{-# OPTIONS --without-K #-}
open import Function
open import Level.NP
open import Data.Product.NP
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Algebra.Monoid
open import HoTT hiding (∙=)
open ≡-Reasoning
open import Algebra.Group

module Algebra.Group.Abelian where

record Abelian-Group-Struct {ℓ} {G : Set ℓ} (grp-ops : Group-Ops G) : Set ℓ where
  constructor _,_
  open Group-Ops grp-ops
  field
    grp-struct : Group-Struct grp-ops
    comm : Commutative _∙_
  open Group-Struct grp-struct public

  open From-Assoc-Comm assoc comm public
    hiding (assoc=; !assoc=; inner=; assocs)

  ⁻¹-hom : ∀ {x y} → (x ∙ y)⁻¹ ≡ x ⁻¹ ∙ y ⁻¹
  ⁻¹-hom = ⁻¹-hom′ ♦ comm

  split-/-∙ : ∀ {x y z t} → (x ∙ y) / (z ∙ t) ≡ (x / z) ∙ (y / t)
  split-/-∙ {x} {y} {z} {t}
    = (x ∙ y) ∙ (z ∙ t)⁻¹      ≡⟨ ∙= idp ⁻¹-hom ⟩
      (x ∙ y) ∙ (z ⁻¹ ∙ t ⁻¹)  ≡⟨  interchange  ⟩
      (x / z) ∙ (y / t)        ∎

  elim-∙-left-/ : ∀ {x y z} → (x ∙ y) / (x ∙ z) ≡ y / z
  elim-∙-left-/ {x} {y} {z}
    = (x ∙ y) / (x ∙ z) ≡⟨ split-/-∙ ⟩
      (x / x) ∙ (y / z) ≡⟨ ∙= (snd inverse) idp ⟩
      ε ∙ (y / z)       ≡⟨ fst identity ⟩
      y / z ∎

record Abelian-Group {ℓ}(G : Set ℓ) : Set ℓ where
  constructor _,_
  field
    grp-ops    : Group-Ops G
    grp-comm   : Abelian-Group-Struct grp-ops
  open Group-Ops    grp-ops    public
  open Abelian-Group-Struct grp-comm public
  grp : Group G
  grp = record { grp-struct = grp-struct }

module Additive-Abelian-Group-Struct
    {ℓ}{G : Set ℓ}{grp-ops : Group-Ops G}
    (grp-comm-struct : Abelian-Group-Struct grp-ops) where
  open Additive-Group-Struct (Abelian-Group-Struct.grp-struct grp-comm-struct) public
  open Abelian-Group-Struct grp-comm-struct public
    using    ()
    renaming ( ⁻¹-hom to 0−-hom
             ; assoc-comm to +-assoc-comm
             ; comm to +-comm
             ; comm= to +-comm=
             ; elim-∙-left-/ to elim-+-left-−
             ; interchange to +-interchange
             ; split-/-∙ to split-−-+
             )

module Additive-Abelian-Group {ℓ}{G : Set ℓ} (grp-comm : Abelian-Group G) where
  open Additive-Group-Ops            (Abelian-Group.grp-ops  grp-comm) public
  open Additive-Abelian-Group-Struct (Abelian-Group.grp-comm grp-comm) public

module Multiplicative-Abelian-Group-Struct
    {ℓ}{G : Set ℓ}{grp-ops : Group-Ops G}
    (grp-comm-struct : Abelian-Group-Struct grp-ops) where
  open Multiplicative-Group-Struct (Abelian-Group-Struct.grp-struct grp-comm-struct) public
  open Abelian-Group-Struct grp-comm-struct public
    using    (⁻¹-hom)
    renaming ( assoc-comm to *-assoc-comm
             ; comm to *-comm
             ; comm= to *-comm=
             ; elim-∙-left-/ to elim-*-left-−
             ; interchange to *-interchange
             ; split-/-∙ to split-/-*
             )

module Multiplicative-Abelian-Group {ℓ}{G : Set ℓ} (grp-comm : Abelian-Group G) where
  open Multiplicative-Group-Ops            (Abelian-Group.grp-ops  grp-comm) public
  open Multiplicative-Abelian-Group-Struct (Abelian-Group.grp-comm grp-comm) public
-- -}
-- -}
-- -}
-- -}
