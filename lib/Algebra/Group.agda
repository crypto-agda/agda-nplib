{-# OPTIONS --without-K #-}
  -- TODO
  -- If you are looking for a proof of:
  --   f (Σ(xᵢ∈A) g(x₁)) ≡ Π(xᵢ∈A) (f(g(xᵢ)))
  -- Have a look to:
  --   https://github.com/crypto-agda/explore/blob/master/lib/Explore/GroupHomomorphism.agda
open import Type using (Type_)
open import Data.Product.NP using (_,_;fst;snd)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Algebra.Raw
open import Algebra.Monoid

module Algebra.Group where

record Group-Struct {ℓ} {G : Type ℓ} (grp-ops : Group-Ops G) : Type ℓ where
  constructor _,_
  open Group-Ops grp-ops
  open From-Group-Ops grp-ops

  -- laws
  field
    mon-struct : Monoid-Struct mon-ops
    inverse    : Inverse ε _⁻¹ _∙_

  mon : Monoid G
  mon = mon-ops , mon-struct

  ⁻¹∙-inverse : LeftInverse ε _⁻¹ _∙_
  ⁻¹∙-inverse = fst inverse

  ∙⁻¹-inverse : RightInverse ε _⁻¹ _∙_
  ∙⁻¹-inverse = snd inverse

  open Monoid-Struct mon-struct                             public
  open From-Assoc-Identities-Inverse assoc identity inverse public

-- TODO Monoid+LeftInverse → Group

record Group {ℓ}(G : Type ℓ) : Type ℓ where
  constructor _,_
  field
    grp-ops    : Group-Ops G
    grp-struct : Group-Struct grp-ops
  open Group-Ops    grp-ops    public
  open Group-Struct grp-struct public

-- A renaming of Group-Struct with additive notation
module Additive-Group-Struct {ℓ}{G : Type ℓ}{grp-ops : Group-Ops G}
                             (grp-struct : Group-Struct grp-ops)
    = Group-Struct grp-struct
    using    ()
    renaming ( mon-struct to +-mon-struct
             ; mon to +-mon
             ; assoc to +-assoc
             ; identity to +-identity
             ; ε∙-identity to 0+-identity
             ; ∙ε-identity to +0-identity
             ; assoc= to +-assoc=
             ; !assoc= to +-!assoc=
             ; inner= to +-inner=
             ; inverse to 0−-inverse
             ; inverseˡ to 0−-inverseˡ
             ; inverseʳ to 0−-inverseʳ
             ; ∙-/ to +-−; /-∙ to −-+
             ; ∙-is-equiv to +-is-equiv
             ; flip-∙-is-equiv to flip-+-is-equiv
             ; unique-ε-left to unique-0-left
             ; unique-ε-right to unique-0-right
             ; x/y≡ε→x≡y to x−y≡0→x≡y
             ; x/y≢ε to x−y≢0
             ; is-ε-left to is-0-left
             ; is-ε-right to is-0-right
             ; unique-⁻¹ to unique-0−
             ; cancels-∙-left to cancels-+-left
             ; cancels-∙-right to cancels-+-right
             ; elim-∙-right-/ to elim-+-right-−
             ; elim-assoc= to elim-+-assoc=
             ; elim-!assoc= to elim-+-!assoc=
             ; elim-inner= to elim-+-inner=
             ; ⁻¹-hom′ to 0−-hom′
             ; ⁻¹-inj to 0−-inj
             ; ⁻¹-involutive to 0−-involutive
             ; ε⁻¹≡ε to 0−0≡0
             ; ε^⁺ to 0⊗⁺
             ; ε^⁻ to 0⊗⁻
             ; ε^  to 0⊗
             )

-- A renaming of Group with additive notation
module Additive-Group {ℓ}{G : Type ℓ}(mon : Group G) where
  open Additive-Group-Ops    (Group.grp-ops    mon) public
  open Additive-Group-Struct (Group.grp-struct mon) public

-- A renaming of Group-Struct with multiplicative notation
module Multiplicative-Group-Struct {ℓ}{G : Type ℓ}{grp-ops : Group-Ops G}
                                   (grp-struct : Group-Struct grp-ops)
  = Group-Struct grp-struct
    using    ( unique-⁻¹
             ; ⁻¹-hom′
             ; ⁻¹-inj
             ; ⁻¹-involutive
             )
    renaming ( assoc to *-assoc
             ; identity to *-identity
             ; ε∙-identity to 1*-identity
             ; ∙ε-identity to *1-identity
             ; inverse to ⁻¹-inverse
             ; ∙-/ to *-/; /-∙ to /-*
             ; mon-struct to *-mon-struct
             ; mon to *-mon
             ; ∙-is-equiv to *-is-equiv
             ; flip-∙-is-equiv to flip-*-is-equiv
             ; unique-ε-left to unique-1-left
             ; unique-ε-right to unique-1-right
             ; x/y≡ε→x≡y to x/y≡1→x≡y
             ; x/y≢ε to x/y≢1
             ; is-ε-left to is-1-left
             ; is-ε-right to is-1-right
             ; cancels-∙-left to cancels-*-left
             ; cancels-∙-right to cancels-*-right
             ; assoc= to *-assoc=
             ; !assoc= to *-!assoc=
             ; inner= to *-inner=
             ; elim-∙-right-/ to elim-*-right-/
             ; elim-assoc= to elim-*-assoc=
             ; elim-!assoc= to elim-*-!assoc=
             ; elim-inner= to elim-*-inner=
             ; ε⁻¹≡ε to 1⁻¹≡1
             ; ε^⁺ to 1^⁺
             ; ε^⁻ to 1^⁻
             ; ε^  to 1^
             )

-- A renaming of Group with multiplicative notation
module Multiplicative-Group {ℓ}{G : Type ℓ}(mon : Group G) where
  open Multiplicative-Group-Ops    (Group.grp-ops    mon) public
  open Multiplicative-Group-Struct (Group.grp-struct mon) public
-- -}
-- -}
-- -}
-- -}
