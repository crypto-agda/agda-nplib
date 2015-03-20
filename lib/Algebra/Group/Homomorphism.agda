module Algebra.Group.Homomorphism where

import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Algebra.Monoid
open import Algebra.Monoid.Homomorphism
open import Algebra.Group
open import Level.NP
open import Data.Product.NP
open import Data.Nat.NP using (ℕ; zero; suc; 1+_)
open import Data.Integer.NP
  hiding (module ℤ+; _⊔_)
  renaming ( _+_ to _+ℤ_; _-_ to _−ℤ_; _*_ to _*ℤ_)
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
open ≡-Reasoning

record GroupHomomorphism {a}{A : Set a}{b}{B : Set b}
                         (grpA0+ : Group A)(grpB1* : Group B)
                         (f : A → B) : Set (a ⊔ b) where
  constructor mk

  open Additive-Group grpA0+
  open Multiplicative-Group grpB1*

  field
    hom : Homomorphic₂ f _+_ _*_

  pres-unit : f 0ᵍ ≡ 1ᵍ
  pres-unit = unique-1ᵍ-left part
    where part = f 0ᵍ * f 0ᵍ  ≡⟨ ! hom ⟩
                 f (0ᵍ + 0ᵍ)  ≡⟨ ap f (fst +-identity) ⟩
                 f 0ᵍ         ∎

  0ᵍ-hom-1ᵍ = pres-unit

  mon-hom : MonoidHomomorphism +-mon *-mon f
  mon-hom = 0ᵍ-hom-1ᵍ , hom

  open MonoidHomomorphism mon-hom public

  pres-inv : ∀ {x} → f (0- x) ≡ (f x)⁻¹
  pres-inv {x} = unique-⁻¹ part
    where part = f (0- x) * f x  ≡⟨ ! hom ⟩
                 f (0- x + x)    ≡⟨ ap f (fst 0--inverse) ⟩
                 f 0ᵍ            ≡⟨ pres-unit ⟩
                 1ᵍ              ∎

  0--⁻¹ = pres-inv

  −-/ : ∀ {x y} → f (x − y) ≡ f x / f y
  −-/ {x} {y} = f (x − y)       ≡⟨ hom ⟩
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

  module ⁻¹-Hom where
    -- The proper type for ⁻¹-hom′
    ⁻¹-hom' : GroupHomomorphism grp (grp ᵒᵖ) _⁻¹
    ⁻¹-hom' = mk ⁻¹-hom′
    open GroupHomomorphism ⁻¹-hom' public

  module ℤ+-^-Hom {b} where
    ^-+-hom : GroupHomomorphism ℤ+-grp grp (_^_ b)
    ^-+-hom = mk (λ {i} {j} → ^-+ i j)

    open GroupHomomorphism ^-+-hom public
