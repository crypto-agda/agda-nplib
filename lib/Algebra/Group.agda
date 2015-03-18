open import Function
open import Data.Product.NP
open import Data.Nat.NP using (ℕ; zero; suc; 1+_)
open import Data.Integer hiding (_+_; _*_)
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
open import Algebra.FunctionProperties.Eq
open import Algebra.Monoid
open ≡-Reasoning

module Algebra.Group where

record Group-Ops {ℓ} (G : Set ℓ) : Set ℓ where
  constructor mk
  infixl 7 _∙_

  field
    _∙_ : G → G → G
    ε   : G
    _⁻¹ : G → G

  mon-ops : Monoid-Ops G
  mon-ops = record { _∙_ = _∙_; ε = ε }

  open Monoid-Ops mon-ops public hiding (_∙_; ε)
  open FromInverseOp _⁻¹  public

record Group-Struct {ℓ} {G : Set ℓ} (grp-ops : Group-Ops G) : Set ℓ where
  constructor mk
  open Group-Ops grp-ops

  -- laws
  field
    assoc    : Associative _∙_
    identity : Identity ε _∙_
    inverse  : Inverse ε _⁻¹ _∙_

  mon-struct : Monoid-Struct mon-ops
  mon-struct = record { assoc = assoc ; identity = identity }

  open Monoid-Struct mon-struct public hiding (assoc; identity)
  open FromRightInverse _⁻¹ (snd inverse) public
  open FromLeftInverse  _⁻¹ (fst inverse) public

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
  open Group-Struct grp-struct public

  open FromAssocComm _∙_ assoc comm public
    hiding (assoc=; !assoc=; inner=)

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

record Abelian-Group (G : Set) : Set where
  field
    grp-ops    : Group-Ops G
    grp-comm   : Abelian-Group-Struct grp-ops
  open Group-Ops    grp-ops    public
  open Abelian-Group-Struct grp-comm public
  grp : Group G
  grp = record { grp-struct = grp-struct }

-- A renaming of Group with additive notation
module Additive-Group {G} (grp : Group G) = Group grp
    renaming ( _∙_ to _+_; ε to 0ᵍ; _⁻¹ to 0-_; _/_ to _−_
             ; _^⁺_ to _⊗⁺_
             ; _^⁻_ to _⊗⁻_
             ; _^_ to _⊗_
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
module Multiplicative-Group {G} (grp : Group G) = Group grp
    using    ( _⁻¹; unique-⁻¹; _/_; /=; ⁻¹-hom′
             ; _^⁺_ ; _^⁻_; _^_ )
    renaming ( _∙_ to _*_; ε to 1ᵍ
             ; assoc to *-assoc; identity to *-identity
             ; inverse to ⁻¹-inverse
             ; ∙-/ to *-/; /-∙ to /-*
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

module Additive-Abelian-Group {G} (grp-comm : Abelian-Group G)
  = Abelian-Group grp-comm
    renaming ( _∙_ to _+_; ε to 0ᵍ; _⁻¹ to 0-_; _/_ to _−_
             ; _^⁺_ to _⊗⁺_
             ; _^⁻_ to _⊗⁻_
             ; _^_ to _⊗_
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

module Multiplicative-Abelian-Group {G} (grp : Abelian-Group G) = Abelian-Group grp
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

  module GroupHomomorphismProp {f}(f-hom : GroupHomomorphism f) where
    f-pres-unit : f 0ᵍ ≡ 1ᵍ
    f-pres-unit = unique-1ᵍ-left part
      where part = f 0ᵍ * f 0ᵍ  ≡⟨ ! f-hom ⟩
                   f (0ᵍ + 0ᵍ)  ≡⟨ ap f (fst +-identity) ⟩
                   f 0ᵍ         ∎

    f-pres-0ᵍ-1ᵍ = f-pres-unit

    f-pres-inv : ∀ {x} → f (0- x) ≡ (f x)⁻¹
    f-pres-inv {x} = unique-⁻¹ part
      where part = f (0- x) * f x  ≡⟨ ! f-hom ⟩
                   f (0- x + x)    ≡⟨ ap f (fst 0--inverse) ⟩
                   f 0ᵍ            ≡⟨ f-pres-unit ⟩
                   1ᵍ              ∎

    f-0--⁻¹ = f-pres-inv

    f-−-/ : ∀ {x y} → f (x − y) ≡ f x / f y
    f-−-/ {x} {y} = f (x − y)       ≡⟨ f-hom ⟩
                    f x * f (0- y)  ≡⟨ ap (_*_ (f x)) f-pres-inv ⟩
                    f x / f y       ∎

    f-hom-iterated⁺ : ∀ {x} n → f (x ⊗⁺ n) ≡ f x ^⁺ n
    f-hom-iterated⁺ zero    = f-pres-unit
    f-hom-iterated⁺ (suc n) = f-hom ♦ *= idp (f-hom-iterated⁺ n)

    f-hom-iterated⁻ : ∀ {x} n → f (x ⊗⁻ n) ≡ f x ^⁻ n
    f-hom-iterated⁻ {x} n =
      f (x ⊗⁻ n)      ≡⟨by-definition⟩
      f (0- (x ⊗⁺ n)) ≡⟨ f-pres-inv ⟩
      f(x ⊗⁺ n)⁻¹     ≡⟨ ap _⁻¹ (f-hom-iterated⁺ n) ⟩
      (f x ^⁺ n)⁻¹    ≡⟨by-definition⟩
      f x ^⁻ n ∎

    f-hom-iterated : ∀ {x} i → f (x ⊗ i) ≡ f x ^ i
    f-hom-iterated -[1+ n ] = f-hom-iterated⁻ (1+ n)
    f-hom-iterated (+ n)    = f-hom-iterated⁺ n

-- -}
-- -}
-- -}
-- -}
