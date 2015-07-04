{-# OPTIONS --without-K #-}
open import Type using (Type_)
open import Function.NP
open import Function.Extensionality
open import Level.NP
open import Data.Product.NP
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open ≡-Reasoning
open import Algebra.Group
open import Algebra.Monoid.Commutative
open import Algebra.Raw
import Algebra.Group.Constructions

module Algebra.Group.Abelian where

record Abelian-Group-Struct {ℓ} {G : Type ℓ} (grp-ops : Group-Ops G) : Type ℓ where
  inductive -- NO_ETA
  constructor _,_
  open Group-Ops grp-ops
  open From-Group-Ops grp-ops
  field
    grp-struct : Group-Struct grp-ops
    comm : Commutative _∙_

  open Group-Struct grp-struct public
    hiding ( ^⁺0-ε; ^⁺1-id; ^⁺2-∙; ^⁺3-∙; ^⁺4-∙; ^⁺-^¹⁺; ^⁺-+; ^⁺-*
           ; assoc; !assoc; !assoc=; assoc=; inner=; assocs
           ; comm-ε; elim-!assoc=; elim-!inner=; elim-assoc=; elim-inner=
           ; identity; is-ε-left; is-ε-right; ε^⁺; ε∙-identity; ∙ε-identity )

  comm-mon-struct : Commutative-Monoid-Struct mon-ops
  comm-mon-struct = mon-struct , comm

  open Commutative-Monoid-Struct comm-mon-struct public
    hiding (comm; mon-struct)

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

record Abelian-Group {ℓ}(G : Type ℓ) : Type ℓ where
  inductive -- NO_ETA
  constructor _,_
  field
    grp-ops    : Group-Ops G
    grp-comm   : Abelian-Group-Struct grp-ops
  open Group-Ops    grp-ops    public
  open Abelian-Group-Struct grp-comm public
  grp : Group G
  grp = record { grp-struct = grp-struct }

module Additive-Abelian-Group-Struct
    {ℓ}{G : Type ℓ}{grp-ops : Group-Ops G}
    (grp-comm-struct : Abelian-Group-Struct grp-ops) where
  open Additive-Group-Struct (Abelian-Group-Struct.grp-struct grp-comm-struct) public
  open Abelian-Group-Struct grp-comm-struct public
    using    (comm-mon-struct)
    renaming ( ⁻¹-hom to 0−-hom
             ; elim-∙-left-/ to elim-+-left-−
             ; split-/-∙ to split-−-+
             )
  open Additive-Commutative-Monoid-Struct comm-mon-struct public
    hiding ( +-identity; +0-identity; 0+-identity; 0⊗⁺; +-assoc; +-!assoc; +-!assoc=
           ; +-assoc=; +-inner=; +-assocs; ^⁺-*; ^⁺-+; ^⁺-^¹⁺; ^⁺0-ε
           ; comm-ε; elim-!assoc=; elim-!inner=; elim-assoc=; elim-inner=
           ; is-ε-left; is-ε-right; ⊗⁺1-id; ⊗⁺2-⊕; ⊗⁺3-⊕; ⊗⁺4-⊕ )

module Additive-Abelian-Group {ℓ}{G : Type ℓ} (grp-comm : Abelian-Group G) where
  open Additive-Group-Ops            (Abelian-Group.grp-ops  grp-comm) public
  open Additive-Abelian-Group-Struct (Abelian-Group.grp-comm grp-comm) public

module Multiplicative-Abelian-Group-Struct
    {ℓ}{G : Type ℓ}{grp-ops : Group-Ops G}
    (grp-comm-struct : Abelian-Group-Struct grp-ops) where
  open Multiplicative-Group-Struct (Abelian-Group-Struct.grp-struct grp-comm-struct) public
  open Abelian-Group-Struct grp-comm-struct public
    using    (⁻¹-hom; comm-mon-struct)
    renaming ( elim-∙-left-/ to elim-*-left-−
             ; split-/-∙ to split-/-*
             )
  open Multiplicative-Commutative-Monoid-Struct comm-mon-struct public
    hiding (*-identity; *1-identity; 1*-identity; 1^⁺; *-assoc; *-!assoc=; *-assoc=; *-inner=; *-assocs
           ; *-!assoc; ^⁺1-id; ^⁺2-∙; ^⁺3-∙; ^⁺4-∙ )

module Multiplicative-Abelian-Group {ℓ}{G : Type ℓ} (grp-comm : Abelian-Group G) where
  open Multiplicative-Group-Ops            (Abelian-Group.grp-ops  grp-comm) public
  open Multiplicative-Abelian-Group-Struct (Abelian-Group.grp-comm grp-comm) public

module Pointwise {{_ : FunExt}}{a}(A : Type a){ℓ}{G : A → Type ℓ}
                 (𝔾 : (x : A) → Abelian-Group (G x)) where
  open Algebra.Group.Constructions.Pointwise A (Abelian-Group.grp ∘ 𝔾)

  abelian-grp-struct : Abelian-Group-Struct grp-ops
  abelian-grp-struct = grp-struct , λ= λ x → Abelian-Group.comm (𝔾 x)

  abelian-grp : Abelian-Group (Π A G)
  abelian-grp = grp-ops , abelian-grp-struct

  open Abelian-Group abelian-grp public

module Pointwise′ {{_ : FunExt}}{a}(A : Type a){ℓ}{G : Type ℓ}
                 (𝔾 : Abelian-Group G) = Pointwise A (λ _ → 𝔾)

module Product {a}{A : Type a}{b}{B : Type b}
               (𝔸 : Abelian-Group A)(𝔹 : Abelian-Group B) where
  open Algebra.Group.Constructions.Product (Abelian-Group.grp 𝔸) (Abelian-Group.grp 𝔹)

  ×-abelian-grp-struct : Abelian-Group-Struct ×-grp-ops
  ×-abelian-grp-struct = ×-grp-struct , ap₂ _,_ (Abelian-Group.comm 𝔸) (Abelian-Group.comm 𝔹)

  ×-abelian-grp : Abelian-Group (A × B)
  ×-abelian-grp = ×-grp-ops , ×-abelian-grp-struct

  -- open Abelian-Group ×-abelian-grp public
-- -}
-- -}
-- -}
-- -}
