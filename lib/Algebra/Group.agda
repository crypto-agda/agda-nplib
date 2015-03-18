{-# OPTIONS --without-K #-}
open import Function
open import Data.Product.NP
open import Data.Nat.NP using (ℕ; zero; suc; 1+_)
open import Data.Integer.NP
  hiding (module ℤ+)
  renaming ( _+_ to _+ℤ_; _-_ to _−ℤ_; _*_ to _*ℤ_)
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
open import Algebra.FunctionProperties.Eq
open import Algebra.Monoid
open import HoTT hiding (∙=)
open ≡-Reasoning

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
  open FromRightInverse _⁻¹ (snd inverse) public
  open FromLeftInverse  _⁻¹ (fst inverse) public

-- TODO Monoid+LeftInverse → Group

record Group {ℓ}(G : Set ℓ) : Set ℓ where
  constructor _,_
  field
    grp-ops    : Group-Ops G
    grp-struct : Group-Struct grp-ops
  open Group-Ops    grp-ops    public
  open Group-Struct grp-struct public

record Abelian-Group-Struct {ℓ} {G : Set ℓ} (grp-ops : Group-Ops G) : Set ℓ where
  constructor _,_
  open Group-Ops grp-ops
  field
    grp-struct : Group-Struct grp-ops
    comm : Commutative _∙_
  open Group-Struct grp-struct public

  open FromAssocComm _∙_ assoc comm public
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

module _ {a}{A : Set a}{b}{B : Set b}
         (grpA0+ : Group A)(grpB1* : Group B) where
  open Additive-Group grpA0+
  open Multiplicative-Group grpB1*

  GroupHomomorphism : (A → B) → Set _
  GroupHomomorphism f = ∀ {x y} → f (x + y) ≡ f x * f y

  -- TODO
  -- If you are looking for a proof of:
  --   f (Σ(xᵢ∈A) g(x₁)) ≡ Π(xᵢ∈A) (f(g(xᵢ)))
  -- Have a look to:
  --   https://github.com/crypto-agda/explore/blob/master/lib/Explore/GroupHomomorphism.agda

  module GroupHomomorphismProp {f}(f-hom : GroupHomomorphism f) where
    pres-unit : f 0ᵍ ≡ 1ᵍ
    pres-unit = unique-1ᵍ-left part
      where part = f 0ᵍ * f 0ᵍ  ≡⟨ ! f-hom ⟩
                   f (0ᵍ + 0ᵍ)  ≡⟨ ap f (fst +-identity) ⟩
                   f 0ᵍ         ∎

    pres-0ᵍ-1ᵍ = pres-unit

    mon-hom : MonoidHomomorphism +-mon *-mon f
    mon-hom = pres-0ᵍ-1ᵍ , f-hom

    open MonoidHomomorphism mon-hom public

    pres-inv : ∀ {x} → f (0- x) ≡ (f x)⁻¹
    pres-inv {x} = unique-⁻¹ part
      where part = f (0- x) * f x  ≡⟨ ! f-hom ⟩
                   f (0- x + x)    ≡⟨ ap f (fst 0--inverse) ⟩
                   f 0ᵍ            ≡⟨ pres-unit ⟩
                   1ᵍ              ∎

    0--⁻¹ = pres-inv

    −-/ : ∀ {x y} → f (x − y) ≡ f x / f y
    −-/ {x} {y} = f (x − y)       ≡⟨ f-hom ⟩
                  f x * f (0- y)  ≡⟨ ap (_*_ (f x)) pres-inv ⟩
                  f x / f y       ∎

    hom-iterated⁻ : ∀ {x} n → f (x ⊗⁻ n) ≡ f x ^⁻ n
    hom-iterated⁻ {x} n =
      f (x ⊗⁻ n)      ≡⟨by-definition⟩
      f (0- (x ⊗⁺ n)) ≡⟨ pres-inv ⟩
      f(x ⊗⁺ n)⁻¹     ≡⟨ ap _⁻¹ (hom-iterated⁺ n) ⟩
      (f x ^⁺ n)⁻¹    ≡⟨by-definition⟩
      f x ^⁻ n ∎

    hom-iterated : ∀ {x} i → f (x ⊗ i) ≡ f x ^ i
    hom-iterated -[1+ n ] = hom-iterated⁻ (1+ n)
    hom-iterated (+ n)    = hom-iterated⁺ n

ℤ+-grp-ops : Group-Ops ℤ
ℤ+-grp-ops = ℤ+-mon-ops , -_

ℤ+-grp-struct : Group-Struct ℤ+-grp-ops
ℤ+-grp-struct = ℤ+-mon-struct
              , (λ{x} → fst ℤ°.-‿inverse x)
              , (λ{x} → snd ℤ°.-‿inverse x)

ℤ+-grp : Group ℤ
ℤ+-grp = _ , ℤ+-grp-struct

module ℤ+ = Additive-Group ℤ+-grp

module _ {ℓ}{G : Set ℓ}(grp : Group G) where
  open Groupᵒᵖ
  open Group grp
  -- The proper type for ⁻¹-hom′
  private
    ⁻¹-hom' : GroupHomomorphism grp (grp ᵒᵖ) _⁻¹
    ⁻¹-hom' = ⁻¹-hom′

  module ℤ+-^-Hom {b} where
    ^-+-hom : GroupHomomorphism ℤ+-grp grp (_^_ b)
    ^-+-hom {i} {j} = ^-+ i j

    open GroupHomomorphismProp ℤ+-grp grp {_^_ b} (λ {i}{j} → ^-+-hom {i}{j}) public
-- -}
-- -}
-- -}
-- -}
