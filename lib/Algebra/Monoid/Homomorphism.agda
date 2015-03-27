{-# OPTIONS --without-K #-}
open import Type using () renaming (Type_ to Type)
open import Level.NP
open import Data.Product.NP
open import Data.Nat
  using    (ℕ; zero)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; suc to 1+_)
import Data.Nat.Properties.Simple as ℕ°
open import Data.Integer.NP
  using    (ℤ; +_; -[1+_]; _⊖_; -_; module ℤ°)
  renaming ( _+_ to _+ℤ_; _-_ to _−ℤ_; _*_ to _*ℤ_
           )
open import Relation.Binary.PropositionalEquality.NP renaming (_∙_ to _♦_)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Algebra.Raw
open import Algebra.Monoid

module Algebra.Monoid.Homomorphism where

record MonoidHomomorphism {a}{A : Type a}{b}{B : Type b}
                          (monA0+ : Monoid A)
                          (monB1* : Monoid B)
                          (f : A → B) : Type(a ⊔ b) where
  constructor _,_
  open Additive-Monoid monA0+
  open Multiplicative-Monoid monB1*
  field
    0-hom-1 : Homomorphic₀ f 0# 1#
    +-hom-* : Homomorphic₂ f _+_ _*_

  hom-iterated⁺ : ∀ {x} n → f (x ⊗⁺ n) ≡ f x ^⁺ n
  hom-iterated⁺ 0      = 0-hom-1
  hom-iterated⁺ (1+ n) = +-hom-* ♦ *= idp (hom-iterated⁺ n)

ℕ+-mon-ops : Monoid-Ops ℕ
ℕ+-mon-ops = _+ℕ_ , 0

ℕ+-mon-struct : Monoid-Struct ℕ+-mon-ops
ℕ+-mon-struct = from-assoc _+ℕ_ (λ {x}{y}{z} → ℕ°.+-assoc x y z)
              , ((λ{x} → idp) , (λ{x} → ℕ°.+-right-identity x))

ℕ+-mon : Monoid ℕ
ℕ+-mon = ℕ+-mon-ops , ℕ+-mon-struct

module ℕ+-mon = Additive-Monoid ℕ+-mon

ℕ*-mon-ops : Monoid-Ops ℕ
ℕ*-mon-ops = _*ℕ_ , 1

ℕ*-mon-struct : Monoid-Struct ℕ*-mon-ops
ℕ*-mon-struct = (from-assoc _*ℕ_ (λ {x}{y}{z} → ℕ°.*-assoc x y z))
              , ( (λ{x} → ℕ°.+-comm x 0)
                , (λ{x} → ℕ°.*-comm x 1 ♦ ℕ°.+-comm x 0))

ℕ*-mon : Monoid ℕ
ℕ*-mon = _ , ℕ*-mon-struct

module ℕ*-mon = Multiplicative-Monoid ℕ*-mon

ℤ+-mon-ops : Monoid-Ops ℤ
ℤ+-mon-ops = _+ℤ_ , + 0

ℤ+-mon-struct : Monoid-Struct ℤ+-mon-ops
ℤ+-mon-struct = (from-assoc _+ℤ_ (λ {x}{y}{z} → ℤ°.+-assoc x y z))
              , (λ{x} → fst ℤ°.+-identity x)
              , (λ{x} → snd ℤ°.+-identity x)

ℤ+-mon : Monoid ℤ
ℤ+-mon = _ , ℤ+-mon-struct

module ℤ+-mon = Additive-Monoid ℤ+-mon

module MonoidHomomorphism^ {ℓ}{M : Type ℓ} (mon : Monoid M) where
  open Monoid mon

  ^⁺-hom : ∀ {b} → MonoidHomomorphism ℕ+-mon mon (_^⁺_ b)
  ^⁺-hom = idp , λ {x}{y} → ^⁺-+ x
