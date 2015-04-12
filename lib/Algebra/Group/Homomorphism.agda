module Algebra.Group.Homomorphism where

open import Type using (Type_)
open import Function.NP using (Op₂; _∘_)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Algebra.Monoid
open import Algebra.Monoid.Homomorphism
open import Algebra.Raw
open import Algebra.Group
open import Algebra.Group.Constructions
open import Level.NP
open import Data.Product.NP
open import Data.Nat.NP     using (1+_)
open import Data.Integer.NP using (ℤ; -[1+_]; +_; -_; module ℤ°)
open import Relation.Binary.PropositionalEquality.NP
open ≡-Reasoning

record GroupHomomorphism {a}{A : Type a}{b}{B : Type b}
                         (grpA0+ : Group A)(grpB1* : Group B)
                         (f : A → B) : Type (a ⊔ b) where
  constructor mk

  open Additive-Group grpA0+
  open Multiplicative-Group grpB1*

  field
    hom : Homomorphic₂ f _+_ _*_

  pres-unit : f 0# ≡ 1#
  pres-unit = unique-1-left part
    where part = f 0# * f 0#  ≡⟨ ! hom ⟩
                 f (0# + 0#)  ≡⟨ ap f (fst +-identity) ⟩
                 f 0#         ∎

  mon-hom : MonoidHomomorphism +-mon *-mon f
  mon-hom = pres-unit , hom

  open MonoidHomomorphism mon-hom public

  pres-inv : ∀ {x} → f (0− x) ≡ (f x)⁻¹
  pres-inv {x} = unique-⁻¹ part
    where part = f (0− x) * f x  ≡⟨ ! hom ⟩
                 f (0− x + x)    ≡⟨ ap f (fst 0−-inverse) ⟩
                 f 0#            ≡⟨ pres-unit ⟩
                 1#              ∎

  0−-⁻¹ = pres-inv

  −-/ : ∀ {x y} → f (x − y) ≡ f x / f y
  −-/ {x} {y} = f (x − y)       ≡⟨ hom ⟩
                f x * f (0− y)  ≡⟨ ap (_*_ (f x)) pres-inv ⟩
                f x / f y       ∎

  hom-iterated⁻ : ∀ {x} n → f (x ⊗⁻ n) ≡ f x ^⁻ n
  hom-iterated⁻ {x} n =
    f (x ⊗⁻ n)      ≡⟨by-definition⟩
    f (0−(x ⊗⁺ n))  ≡⟨ pres-inv ⟩
    f(x ⊗⁺ n)⁻¹     ≡⟨ ap _⁻¹ (hom-iterated⁺ n) ⟩
    (f x ^⁺ n)⁻¹    ≡⟨by-definition⟩
    f x ^⁻ n        ∎

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

module _ {ℓ}{G : Type ℓ}(𝔾 : Group G) where
  open Groupᵒᵖ
  open Group 𝔾

  module ⁻¹-Hom where
    -- The proper type for ⁻¹-hom′
    ⁻¹-hom' : GroupHomomorphism 𝔾 (𝔾 ᵒᵖ) _⁻¹
    ⁻¹-hom' = mk ⁻¹-hom′
    open GroupHomomorphism ⁻¹-hom' public

  module ℤ+-^-Hom {b} where
    ^-+-hom : GroupHomomorphism ℤ+-grp 𝔾 (_^_ b)
    ^-+-hom = mk (λ {i} {j} → ^-+ i j)

    open GroupHomomorphism ^-+-hom public

module Stability-Minimal
  {a}{A  : Type a}
  {b}{B  : Type b}
  (φ     : A → B)
  (_+_   : Op₂ A)
  (_*_   : Op₂ B)
  (φ-+-* : ∀ {x y} → φ (x + y) ≡ φ x * φ y)
  {c}{C  : Type c}
  (F     : (A → B) → C)
  (F=    : ∀ {f g : A → B} → f ≗ g → F f ≡ F g)
  (Fφ*   : ∀ {k} → F φ ≡ F (_*_ k ∘ φ))
  where

  +-stable : ∀ {k} → F φ ≡ F (φ ∘ _+_ k)
  +-stable {k} =
    F φ                ≡⟨ Fφ* ⟩
    F (_*_ (φ k) ∘ φ)  ≡⟨ F= (λ x → ! φ-+-*) ⟩
    F (φ ∘ _+_ k)      ∎

module Stability
  {a}{A  : Type a}
  {b}{B  : Type b}
  (G+ : Group A)
  (G* : Group B)
  (φ : A → B)
  (φ-hom : GroupHomomorphism G+ G* φ)
  where
  open Additive-Group G+
  open Multiplicative-Group G*
  open GroupHomomorphism φ-hom

  open Stability-Minimal φ _+_ _*_ hom public
-- -}
-- -}
-- -}
-- -}
