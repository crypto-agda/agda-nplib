open import Function
open import Data.Product.NP
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
open import Algebra.FunctionProperties.Eq
open ≡-Reasoning

module Algebra.Group where

record Group-Ops {ℓ} (G : Set ℓ) : Set ℓ where
  infixl 7 _∙_ _/_

  field
    _∙_ : G → G → G
    ε   : G
    _⁻¹ : G → G

  _/_ : G → G → G
  x / y = x ∙ y ⁻¹

record Group-Struct {ℓ} {G : Set ℓ} (grp-ops : Group-Ops G) : Set ℓ where
  open Group-Ops grp-ops

  -- laws
  field
    assoc    : Associative _∙_
    identity : Identity ε _∙_
    inverse  : Inverse ε _⁻¹ _∙_

  ∙= : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x ∙ y ≡ x' ∙ y'
  ∙= {x} {y' = y'} p q = ap (_∙_ x) q ♦ ap (λ z → z ∙ y') p

  /= : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x / y ≡ x' / y'
  /= {x} {y' = y'} p q = ap (_/_ x) q ♦ ap (λ z → z / y') p

  ∙-/ : ∀ {x y} → x ≡ (x ∙ y) / y
  ∙-/ {x} {y}
    = x            ≡⟨ ! snd identity ⟩
      x ∙ ε        ≡⟨ ap (_∙_ x) (! snd inverse) ⟩
      x ∙ (y / y)  ≡⟨ ! assoc ⟩
      (x ∙ y) / y  ∎

  /-∙ : ∀ {x y} → x ≡ (x / y) ∙ y
  /-∙ {x} {y}
    = x               ≡⟨ ! snd identity ⟩
      x ∙ ε           ≡⟨ ap (_∙_ x) (! fst inverse) ⟩
      x ∙ (y ⁻¹ ∙ y)  ≡⟨ ! assoc ⟩
      (x / y) ∙ y     ∎

  unique-ε : ∀ {x y} → x ∙ y ≡ y → x ≡ ε
  unique-ε {x} {y} eq
    = x            ≡⟨ ∙-/ ⟩
      (x ∙ y) / y  ≡⟨ /= eq idp ⟩
      y / y        ≡⟨ snd inverse ⟩
      ε            ∎

  unique-⁻¹ : ∀ {x y} → x ∙ y ≡ ε → x ≡ y ⁻¹
  unique-⁻¹ {x} {y} eq
    = x            ≡⟨ ∙-/ ⟩
      (x ∙ y) / y  ≡⟨ /= eq idp ⟩
      ε / y        ≡⟨ fst identity ⟩
      y ⁻¹         ∎

  cancels-∙ : ∀ {x y z} → x ∙ y ≡ x ∙ z → y ≡ z
  cancels-∙ {x} {y} {z} e
    = y              ≡⟨ ! fst identity ⟩
      ε ∙ y          ≡⟨ ∙= (! fst inverse) idp ⟩
      x ⁻¹ ∙ x ∙ y   ≡⟨ assoc ⟩
      x ⁻¹ ∙ (x ∙ y) ≡⟨ ∙= idp e ⟩
      x ⁻¹ ∙ (x ∙ z) ≡⟨ ! assoc ⟩
      x ⁻¹ ∙ x ∙ z   ≡⟨ ∙= (fst inverse) idp ⟩
      ε ∙ z          ≡⟨ fst identity ⟩
      z ∎

  ⁻¹-hom′ : ∀ {x y} → (x ∙ y)⁻¹ ≡ y ⁻¹ ∙ x ⁻¹
  ⁻¹-hom′ {x} {y} = cancels-∙ {x ∙ y}
     ((x ∙ y) ∙ (x ∙ y)⁻¹     ≡⟨ snd inverse ⟩
      ε                       ≡⟨ ! snd inverse ⟩
      x ∙ x ⁻¹                ≡⟨ ap (_∙_ x) (! fst identity) ⟩
      x ∙ (ε ∙ x ⁻¹)          ≡⟨ ∙= idp (∙= (! snd inverse) idp) ⟩
      x ∙ ((y ∙ y ⁻¹) ∙ x ⁻¹) ≡⟨ ap (_∙_ x) assoc ⟩
      x ∙ (y ∙ (y ⁻¹ ∙ x ⁻¹)) ≡⟨ ! assoc ⟩
      (x ∙ y) ∙ (y ⁻¹ ∙ x ⁻¹) ∎)

record Group (G : Set) : Set where
  field
    grp-ops    : Group-Ops G
    grp-struct : Group-Struct grp-ops
  open Group-Ops    grp-ops    public
  open Group-Struct grp-struct public

record Abelian-Group-Struct {ℓ} {G : Set ℓ} (grp-ops : Group-Ops G) : Set ℓ where
  open Group-Ops grp-ops
  field
    grp-struct : Group-Struct grp-ops
    comm : Commutative _∙_
  open Group-Struct grp-struct

  assoc-comm : ∀ {x y z} → x ∙ (y ∙ z) ≡ y ∙ (x ∙ z)
  assoc-comm = ! assoc ♦ ∙= comm idp ♦ assoc

  interchange : Interchange _∙_ _∙_
  interchange = InterchangeFromAssocComm.·-interchange _∙_ assoc comm

  ⁻¹-hom : ∀ {x y} → (x ∙ y)⁻¹ ≡ x ⁻¹ ∙ y ⁻¹
  ⁻¹-hom = ⁻¹-hom′ ♦ comm

  split-/-∙ : ∀ {x y z t} → (x ∙ y) / (z ∙ t) ≡ (x / z) ∙ (y / t)
  split-/-∙ {x} {y} {z} {t}
    = (x ∙ y)    / (z ∙ t)       ≡⟨by-definition⟩
      (x ∙ y)    ∙ (z ∙ t)⁻¹     ≡⟨ ∙= idp ⁻¹-hom ⟩
      (x ∙ y)    ∙ (z ⁻¹ ∙ t ⁻¹) ≡⟨ assoc ⟩
      x ∙ (y    ∙ (z ⁻¹ ∙ t ⁻¹)) ≡⟨ ∙= idp assoc-comm ⟩
      x ∙ (z ⁻¹ ∙ (y ∙ t ⁻¹))    ≡⟨ ! assoc ⟩
      (x ∙ z ⁻¹) ∙ (y ∙ t ⁻¹)    ≡⟨by-definition⟩
      (x / z) ∙ (y / t) ∎

  cancels-/ : ∀ {x y z} → (x ∙ y) / (x ∙ z) ≡ y / z
  cancels-/ {x} {y} {z}
    = (x ∙ y) / (x ∙ z) ≡⟨ split-/-∙ ⟩
      (x / x) ∙ (y / z) ≡⟨ ap (λ u →  u ∙ (y / z)) (snd inverse) ⟩
      ε ∙ (y / z)       ≡⟨ fst identity ⟩
      y / z ∎

record Abelian-Group (G : Set) : Set where
  field
    grp-ops    : Group-Ops G
    grp-comm   : Abelian-Group-Struct grp-ops
  open Group-Ops    grp-ops    public
  open Abelian-Group-Struct grp-comm public
  open Group-Struct grp-struct public
  grp : Group G
  grp = record { grp-struct = grp-struct }

-- A renaming of Group with additive notation
module Additive-Group {G} (grp : Group G) = Group grp
    renaming ( _∙_ to _+_; ε to 0ᵍ; _⁻¹ to 0-_; _/_ to _−_
             ; assoc to +-assoc; identity to +-identity
             ; inverse to 0--inverse
             ; ∙-/ to +-−; /-∙ to −-+; unique-ε to unique-0ᵍ; unique-⁻¹ to unique-0-
             ; cancels-∙ to cancels-+
             ; ⁻¹-hom′ to 0--hom′
             ; ∙= to +=; /= to −=)

-- A renaming of Group with multiplicative notation
module Multiplicative-Group {G} (grp : Group G) = Group grp
    using    ( _⁻¹; unique-⁻¹; _/_; /=; ⁻¹-hom′ )
    renaming ( _∙_ to _*_; ε to 1ᵍ
             ; assoc to *-assoc; identity to *-identity
             ; inverse to ⁻¹-inverse
             ; ∙-/ to *-/; /-∙ to /-*; unique-ε to unique-1ᵍ
             ; cancels-∙ to cancels-*
             ; ∙= to *= )

module Additive-Abelian-Group {G} (grp-comm : Abelian-Group G)
  = Abelian-Group grp-comm
    renaming ( _∙_ to _+_; ε to 0ᵍ; _⁻¹ to 0-_; _/_ to _−_
             ; assoc to +-assoc; identity to +-identity
             ; inverse to 0--inverse
             ; ∙-/ to +-−; /-∙ to −-+; unique-ε to unique-0ᵍ; unique-⁻¹ to unique-0-
             ; ∙= to +=; /= to −=
             ; assoc-comm to +-assoc-comm
             ; interchange to +-interchange
             ; ⁻¹-hom to 0--hom
             ; split-/-∙ to split-−-+
             ; cancels-/ to cancels-−)

module Multiplicative-Abelian-Group {G} (grp : Abelian-Group G) = Abelian-Group grp
    using    ( _⁻¹; unique-⁻¹; _/_; /=; ⁻¹-hom′
             ; ⁻¹-hom
             ; cancels-/ )
    renaming ( _∙_ to _*_; ε to 1ᵍ
             ; assoc to *-assoc; identity to *-identity
             ; inverse to ⁻¹-inverse
             ; ∙-/ to *-/; /-∙ to /-*; unique-ε to unique-1ᵍ
             ; cancels-∙ to cancels-*
             ; ∙= to *=
             ; assoc-comm to *-assoc-comm
             ; interchange to *-interchange
             ; split-/-∙ to split-/-* )

module _ {A B : Set}(grpA0+ : Group A)(grpB1* : Group B) where
  open Additive-Group grpA0+
  open Multiplicative-Group grpB1*

  GroupHomomorphism : (A → B) → Set
  GroupHomomorphism f = ∀ {x y} → f (x + y) ≡ f x * f y

  -- TODO
  -- If you are looking for a proof of:
  --   f (Σ(xᵢ∈A) g(x₁)) ≡ Π(xᵢ∈A) (f(g(xᵢ)))
  -- Have a look to:
  --   https://github.com/crypto-agda/explore/blob/master/lib/Explore/GroupHomomorphism.agda

  module GroupHomomorphismProp {f}(f-homo : GroupHomomorphism f) where
    f-pres-unit : f 0ᵍ ≡ 1ᵍ
    f-pres-unit = unique-1ᵍ part
      where part = f 0ᵍ * f 0ᵍ  ≡⟨ ! f-homo ⟩
                   f (0ᵍ + 0ᵍ)  ≡⟨ ap f (fst +-identity) ⟩
                   f 0ᵍ         ∎

    f-pres-0ᵍ-1ᵍ = f-pres-unit

    f-pres-inv : ∀ {x} → f (0- x) ≡ (f x)⁻¹
    f-pres-inv {x} = unique-⁻¹ part
      where part = f (0- x) * f x  ≡⟨ ! f-homo ⟩
                   f (0- x + x)    ≡⟨ ap f (fst 0--inverse) ⟩
                   f 0ᵍ            ≡⟨ f-pres-unit ⟩
                   1ᵍ              ∎

    f-0--⁻¹ = f-pres-inv

    f-−-/ : ∀ {x y} → f (x − y) ≡ f x / f y
    f-−-/ {x} {y} = f (x − y)       ≡⟨ f-homo ⟩
                    f x * f (0- y)  ≡⟨ ap (_*_ (f x)) f-pres-inv ⟩
                    f x / f y       ∎

-- -}
-- -}
-- -}
-- -}
