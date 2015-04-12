{-# OPTIONS --without-K #-}
open import Type using (Type_)
open import Level.NP
open import Function.NP
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality.NP
open ≡-Reasoning

module Algebra.Group.Isomorphism where

open import Algebra.Group
open import Algebra.Group.Homomorphism
  hiding (module Stability; module Stability-Minimal)

record GroupIsomorphism
         {a}{A : Type a}
         {b}{B : Type b}
         (G+   : Group A)
         (G*   : Group B) : Set(a ⊔ b) where
  open Additive-Group G+
  open Multiplicative-Group G*

  field
    φ : A → B -- TODO
    φ-+-* : ∀ {x y} → φ (x + y) ≡ φ x * φ y
    φ⁻¹   : B → A
    φ⁻¹-φ : ∀ {x} → φ⁻¹ (φ x) ≡ x
    φ-φ⁻¹ : ∀ {x} → φ (φ⁻¹ x) ≡ x

  φ-hom : GroupHomomorphism G+ G* φ
  φ-hom = mk φ-+-*

  open GroupHomomorphism φ-hom public

{- How this proof can be used for crypto, in particular ElGamal to DDH

  the Group A is ℤq with modular addition as operation
  the Group B is the cyclic group with order q

  φ is g^, the proof only need that it is a group homomorphism
  and that it has a right inverse

  F is the summation operator and is required to be stable
  under addition of A.

  F should respects extensionality

  This proof adds φ⁻¹ k, because adding a constant is stable under
  the big op F, this addition can then be pulled homomorphically
  through f, to become a, multiplication by k.
-}
module Stability-Minimal
  {a}{A  : Type a}
  {b}{B  : Type b}
  (φ     : A → B)
  (φ⁻¹   : B → A)
  (φ-φ⁻¹ : ∀ {x} → φ (φ⁻¹ x) ≡ x)
  (_+_   : Op₂ A)
  (_*_   : Op₂ B)
  (φ-+-* : ∀ {x y} → φ (x + y) ≡ φ x * φ y)
  {c}{C  : Type c}
  (F     : (A → B) → C)
  (F=    : ∀ {f g : A → B} → f ≗ g → F f ≡ F g)
  where

  module _ (Fφ+ : ∀ {k} → F φ ≡ F (φ ∘ _+_ k)) where

    *-stable : ∀ {k} → F φ ≡ F (_*_ k ∘ φ)
    *-stable {k} =
      F φ                  ≡⟨ Fφ+ ⟩
      F (φ ∘ _+_ (φ⁻¹ k))  ≡⟨ F= (λ x → φ (φ⁻¹ k + x)   ≡⟨ φ-+-* ⟩
                                         φ (φ⁻¹ k) * φ x ≡⟨ ap₂ _*_ φ-φ⁻¹ idp ⟩
                                         k * φ x         ∎) ⟩
      F (_*_ k ∘ φ)        ∎

  {- The reverse direction comes from the homomorphism -}
  open Algebra.Group.Homomorphism.Stability-Minimal
    φ _+_ _*_ φ-+-* F F=

  stability : (∀ {k} → F φ ≡ F (φ ∘ _+_ k)) ↔ (∀ {k} → F φ ≡ F (_*_ k ∘ φ))
  stability = *-stable , +-stable

module Stability
  {a}{A  : Type a}
  {b}{B  : Type b}
  (G+ : Group A)
  (G* : Group B)
  (φ-iso : GroupIsomorphism G+ G*)
  where
  open Additive-Group G+
  open Multiplicative-Group G*
  open GroupIsomorphism φ-iso

  open Stability-Minimal φ φ⁻¹ φ-φ⁻¹ _+_ _*_ φ-+-* public

-- -}
-- -}
-- -}
-- -}
