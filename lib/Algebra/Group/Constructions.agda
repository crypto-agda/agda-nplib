{-# OPTIONS --without-K #-}
open import Type using (Type_)
open import Function.NP
open import Function.Extensionality
open import Data.Product.NP
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Relation.Binary.PropositionalEquality.NP
open import Algebra.Monoid hiding (module Product; module Pointwise; module Pointwise′)
open import Algebra.Raw
open import Algebra.Group

module Algebra.Group.Constructions where

module Groupᵒᵖ {ℓ}{G : Type ℓ} where
  _ᵒᵖ-ops : Endo (Group-Ops G)
  (mon , inv) ᵒᵖ-ops = mon Monoidᵒᵖ.ᵒᵖ-ops , inv

  _ᵒᵖ-struct : {mon : Group-Ops G} → Group-Struct mon → Group-Struct (mon ᵒᵖ-ops)
  (mon , inv) ᵒᵖ-struct = mon Monoidᵒᵖ.ᵒᵖ-struct , swap inv

  _ᵒᵖ : Endo (Group G)
  (ops , struct)ᵒᵖ = _ , struct ᵒᵖ-struct

  ᵒᵖ∘ᵒᵖ-id : ∀ {grp} → (grp ᵒᵖ) ᵒᵖ ≡ grp
  ᵒᵖ∘ᵒᵖ-id = idp

module Product {a}{A : Type a}{b}{B : Type b}
               (𝔸 : Group A)(𝔹 : Group B) where
  open Additive-Group 𝔸
  open Multiplicative-Group 𝔹

  open Algebra.Monoid.Product +-mon *-mon

  ×-grp-ops : Group-Ops (A × B)
  ×-grp-ops = ×-mon-ops , map 0−_ _⁻¹

  ×-grp-struct : Group-Struct ×-grp-ops
  ×-grp-struct = ×-mon-struct
               , ( ap₂ _,_ (fst 0−-inverse) (fst ⁻¹-inverse)
                 , ap₂ _,_ (snd 0−-inverse) (snd ⁻¹-inverse))

  ×-grp : Group (A × B)
  ×-grp = ×-grp-ops , ×-grp-struct

module _ {a}{A : Type a}(𝔸 : Group A){b}{B : Type b}(𝔹 : Group B) where
  open Product
  open Groupᵒᵖ
  ×-ᵒᵖ : (×-grp 𝔸 𝔹)ᵒᵖ ≡ ×-grp (𝔸 ᵒᵖ) (𝔹 ᵒᵖ)
  ×-ᵒᵖ = idp

{-
This module shows how properties of a group 𝔾 are carried on
functions from any type A to 𝔾.
However since the function type can be dependent this also generalises
the product of groups (since Π 𝟚 [ A , B ] ≃ A × B).
-}
module Pointwise {{_ : FunExt}}{a}(A : Type a){ℓ}{G : A → Type ℓ}
                 (𝔾 : (x : A) → Group (G x)) where
  private
    module 𝔾 {x} = Group (𝔾 x)
  open 𝔾 hiding (mon-ops; mon-struct; grp-ops; grp-struct)
  open Algebra.Monoid.Pointwise A (λ x → mon {x})

  _⁽⁻¹⁾ : Op₁ (Π A G)
  (f ⁽⁻¹⁾) x = (f x)⁻¹

  grp-ops : Group-Ops (Π A G)
  grp-ops = mon-ops , _⁽⁻¹⁾

  grp-struct : Group-Struct grp-ops
  grp-struct = mon-struct , λ=ⁱ (fst inverse) , λ=ⁱ (snd inverse)

  grp : Group (Π A G)
  grp = grp-ops , grp-struct

  open Group grp public hiding (grp-ops; grp-struct)

module Pointwise′ {{_ : FunExt}}{a}(A : Type a){m}{G : Type m}(𝔾 : Group G) =
  Pointwise A (λ _ → 𝔾)

module _ {a}{A : Type a}{ℓ}{G : A → Type ℓ} where
  open Groupᵒᵖ
  _⁽ᵒᵖ⁾ : Op₁ (Π A (Group ∘ G))
  (𝔾 ⁽ᵒᵖ⁾) x = (𝔾 x)ᵒᵖ

module _ {{_ : FunExt}}{a}{A : Type a}{ℓ}{G : A → Type ℓ}(𝔾 : (x : A) → Group (G x)) where
  Π-Grp = Pointwise.grp A
  open Groupᵒᵖ

  Π-ᵒᵖ : (Π-Grp 𝔾)ᵒᵖ ≡ Π-Grp (𝔾 ⁽ᵒᵖ⁾)
  Π-ᵒᵖ = idp

{-
  open import Data.Vec
  GroupVec : ∀ n → Group (Vec A n)
  GroupVec n = record { grp-ops = {!!} ; grp-struct = {!!} }
    module GroupVec where
-}
