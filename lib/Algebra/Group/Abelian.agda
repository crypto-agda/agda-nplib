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

  open FromAssocComm assoc comm public
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

module Additive-Abelian-Group {ℓ}{G : Set ℓ} (grp-comm : Abelian-Group G)
  = Abelian-Group grp-comm
    renaming ( _∙_ to _+_; ε to 0ᵍ; _⁻¹ to 0-_; _/_ to _−_
             ; _^⁺_ to _⊗⁺_
             ; _^⁻_ to _⊗⁻_
             ; _^_ to _⊗_
             ; mon-ops to +-mon-ops
             ; mon-struct to +-mon-struct
             ; mon to +-mon
             ; assoc to +-assoc; identity to +-identity
             ; inverse to 0--inverse
             ; ∙-/ to +-−; /-∙ to −-+
             ; unique-ε-left to unique-0ᵍ-left
             ; unique-ε-right to unique-0ᵍ-right
             ; is-ε-left to is-0ᵍ-left
             ; is-ε-right to is-0ᵍ-right
             ; ∙= to +=; /= to −=
             ; assoc-comm to +-assoc-comm
             ; interchange to +-interchange
             ; ⁻¹-hom to 0--hom
             ; split-/-∙ to split-−-+
             ; elim-∙-right-/ to elim-+-right-−
             ; elim-∙-left-/ to elim-+-left-−
             ; elim-assoc= to elim-+-assoc=
             ; elim-!assoc= to elim-+-!assoc=
             ; elim-inner= to elim-+-inner=
             )

module Multiplicative-Abelian-Group {ℓ}{G : Set ℓ} (grp : Abelian-Group G) = Abelian-Group grp
    using    ( _⁻¹; unique-⁻¹
             ; _/_
             ; /=
             ; ⁻¹-hom′
             ; ⁻¹-hom
             ; _^⁺_ ; _^⁻_; _^_
             )
    renaming ( _∙_ to _*_
             ; ε to 1ᵍ
             ; assoc to *-assoc
             ; identity to *-identity
             ; inverse to ⁻¹-inverse
             ; mon-ops to *-mon-ops
             ; mon-struct to *-mon-struct
             ; mon to *-mon
             ; ∙-/ to *-/
             ; /-∙ to /-*
             ; unique-ε-left to unique-1ᵍ-left
             ; unique-ε-right to unique-1ᵍ-right
             ; is-ε-left to is-1ᵍ-left
             ; is-ε-right to is-1ᵍ-right
             ; cancels-∙-left to cancels-*-left
             ; ∙= to *=
             ; assoc= to *-assoc=
             ; !assoc= to *-!assoc=
             ; inner= to *-inner=
             ; outer= to *-outer=
             ; assoc-comm to *-assoc-comm
             ; interchange to *-interchange
             ; split-/-∙ to split-/-*
             ; elim-∙-left-/ to elim-*-left-/
             ; elim-∙-right-/ to elim-*-right-/
             ; elim-assoc= to elim-*-assoc=
             ; elim-!assoc= to elim-*-!assoc=
             ; elim-inner= to elim-*-inner=
             )
