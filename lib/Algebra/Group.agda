{-# OPTIONS --without-K #-}
open import Function
open import Level.NP
open import Data.Product.NP
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Algebra.Monoid
open import Relation.Binary.PropositionalEquality.NP hiding (_∙_)

module Algebra.Group where

record Group-Ops {ℓ} (G : Set ℓ) : Set ℓ where
  constructor _,_

  field
    mon-ops : Monoid-Ops G
    _⁻¹     : G → G

  open Monoid-Ops mon-ops public
  open FromInverseOp _⁻¹  public

record Group-Struct {ℓ} {G : Set ℓ} (grp-ops : Group-Ops G) : Set ℓ where
  constructor _,_
  open Group-Ops grp-ops

  -- laws
  field
    mon-struct : Monoid-Struct mon-ops
    inverse    : Inverse ε _⁻¹ _∙_

  mon : Monoid G
  mon = mon-ops , mon-struct

  open Monoid-Struct mon-struct           public
  open FromIdentitiesAssoc idl idr assoc  public
  open FromRightInverse (snd inverse) public
  open FromLeftInverse  (fst inverse) public

-- TODO Monoid+LeftInverse → Group

record Group {ℓ}(G : Set ℓ) : Set ℓ where
  constructor _,_
  field
    grp-ops    : Group-Ops G
    grp-struct : Group-Struct grp-ops
  open Group-Ops    grp-ops    public
  open Group-Struct grp-struct public

-- A renaming of Group-Ops with additive notation
module Additive-Group-Ops {ℓ}{G : Set ℓ} (grp : Group-Ops G) = Group-Ops grp
    renaming ( _∙_ to _+_; ε to 0ᵍ; _⁻¹ to 0-_; _/_ to _−_
             ; _^⁺_ to _⊗⁺_
             ; _^⁻_ to _⊗⁻_
             ; _^_ to _⊗_
             ; mon-ops to +-mon-ops
             ; ∙= to +=; /= to −=)

-- A renaming of Group with additive notation
module Additive-Group {ℓ}{G : Set ℓ} (grp : Group G) = Group grp
    renaming ( _∙_ to _+_; ε to 0ᵍ; _⁻¹ to 0-_; _/_ to _−_
             ; _^⁺_ to _⊗⁺_
             ; _^⁻_ to _⊗⁻_
             ; _^_ to _⊗_
             ; mon-ops to +-mon-ops
             ; mon-struct to +-mon-struct
             ; mon to +-mon
             ; assoc to +-assoc; identity to +-identity
             ; assoc= to +-assoc=
             ; !assoc= to +-!assoc=
             ; inner= to +-inner=
             ; inverse to 0--inverse
             ; ∙-/ to +-−; /-∙ to −-+
             ; unique-ε-left to unique-0ᵍ-left
             ; unique-ε-right to unique-0ᵍ-right
             ; is-ε-left to is-0ᵍ-left
             ; is-ε-right to is-0ᵍ-right
             ; unique-⁻¹ to unique-0-
             ; cancels-∙-left to cancels-+-left
             ; cancels-∙-right to cancels-+-right
             ; elim-∙-right-/ to elim-+-right-−
             ; elim-assoc= to elim-+-assoc=
             ; elim-!assoc= to elim-+-!assoc=
             ; elim-inner= to elim-+-inner=
             ; ⁻¹-hom′ to 0--hom′
             ; ∙= to +=; /= to −=)

-- A renaming of Group with multiplicative notation
module Multiplicative-Group-Ops {ℓ}{G : Set ℓ} (grp : Group-Ops G) = Group-Ops grp
    using    ( _⁻¹; _/_; /=; _^⁺_ ; _^⁻_; _^_ )
    renaming ( _∙_ to _*_; ε to 1ᵍ; mon-ops to *-mon-ops; ∙= to *= )

-- A renaming of Group with multiplicative notation
module Multiplicative-Group {ℓ}{G : Set ℓ} (grp : Group G) = Group grp
    using    ( _⁻¹; unique-⁻¹; _/_; /=; ⁻¹-hom′
             ; _^⁺_ ; _^⁻_; _^_ )
    renaming ( _∙_ to _*_; ε to 1ᵍ
             ; assoc to *-assoc; identity to *-identity
             ; inverse to ⁻¹-inverse
             ; ∙-/ to *-/; /-∙ to /-*
             ; mon-ops to *-mon-ops
             ; mon-struct to *-mon-struct
             ; mon to *-mon
             ; unique-ε-left to unique-1ᵍ-left
             ; unique-ε-right to unique-1ᵍ-right
             ; is-ε-left to is-1ᵍ-left
             ; is-ε-right to is-1ᵍ-right
             ; cancels-∙-left to cancels-*-left
             ; cancels-∙-right to cancels-*-right
             ; assoc= to *-assoc=
             ; !assoc= to *-!assoc=
             ; inner= to *-inner=
             ; elim-∙-right-/ to elim-*-right-/
             ; elim-assoc= to elim-*-assoc=
             ; elim-!assoc= to elim-*-!assoc=
             ; elim-inner= to elim-*-inner=
             ; ∙= to *= )

module Groupᵒᵖ {ℓ}{G : Set ℓ} where
  _ᵒᵖ-ops : Group-Ops G → Group-Ops G
  (mon , inv) ᵒᵖ-ops = mon Monoidᵒᵖ.ᵒᵖ-ops , inv

  _ᵒᵖ-struct : {mon : Group-Ops G} → Group-Struct mon → Group-Struct (mon ᵒᵖ-ops)
  (mon , inv) ᵒᵖ-struct = mon Monoidᵒᵖ.ᵒᵖ-struct , swap inv

  _ᵒᵖ : Group G → Group G
  (ops , struct)ᵒᵖ = _ , struct ᵒᵖ-struct

  ᵒᵖ∘ᵒᵖ-id : ∀ {grp} → (grp ᵒᵖ) ᵒᵖ ≡ grp
  ᵒᵖ∘ᵒᵖ-id = idp

module GroupProduct {a}{A : Set a}{b}{B : Set b}
                    (grpA0+ : Group A)(grpB1* : Group B) where
  open Additive-Group grpA0+
  open Multiplicative-Group grpB1*

  open MonoidProduct +-mon *-mon

  ×-grp-ops : Group-Ops (A × B)
  ×-grp-ops = ×-mon-ops , map 0-_ _⁻¹

  ×-grp-struct : Group-Struct ×-grp-ops
  ×-grp-struct = ×-mon-struct
               , ( ap₂ _,_ (fst 0--inverse) (fst ⁻¹-inverse)
                 , ap₂ _,_ (snd 0--inverse) (snd ⁻¹-inverse))

  ×-grp : Group (A × B)
  ×-grp = ×-grp-ops , ×-grp-struct

module _ {a}{A : Set a}{b}{B : Set b} where
  open GroupProduct
  open Groupᵒᵖ
  ×-ᵒᵖ : (gA : Group A)(gB : Group B) → (×-grp gA gB)ᵒᵖ ≡ ×-grp (gA ᵒᵖ) (gB ᵒᵖ)
  ×-ᵒᵖ gA gB = idp

{-
  open import Data.Vec
  GroupVec : ∀ n → Group (Vec A n)
  GroupVec n = record { grp-ops = {!!} ; grp-struct = {!!} }
    module GroupVec where
-}

  -- TODO
  -- If you are looking for a proof of:
  --   f (Σ(xᵢ∈A) g(x₁)) ≡ Π(xᵢ∈A) (f(g(xᵢ)))
  -- Have a look to:
  --   https://github.com/crypto-agda/explore/blob/master/lib/Explore/GroupHomomorphism.agda
-- -}
-- -}
-- -}
-- -}
