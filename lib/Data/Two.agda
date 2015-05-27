{-# OPTIONS --without-K #-}
module Data.Two where

open import Data.Two.Base public
open import Data.Bool.Properties
  public
  using (isCommutativeSemiring-∨-∧
        ;commutativeSemiring-∨-∧
        ;module RingSolver
        ;isCommutativeSemiring-∧-∨
        ;commutativeSemiring-∧-∨
        ;isBooleanAlgebra
        ;booleanAlgebra
        ;commutativeRing-xor-∧
        ;module XorRingSolver
        ;not-involutive
        ;not-¬
        ;¬-not
        ;⇔→≡
        ;proof-irrelevance)
  renaming
        (T-≡ to ✓-≡
        ;T-∧ to ✓-∧
        ;T-∨ to ✓-∨)

open import Type using (★_)

open import Algebra
  using (module CommutativeRing; module CommutativeSemiring)

open import Function.Equivalence using (module Equivalence)
open import Function.NP          using (id; _∘_; _⟨_⟩°_; Op₁; Op₂)

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; refl; _∙_)

open import HoTT
open Equivalences

open Equivalence using (to; from)

module Xor° = CommutativeRing     commutativeRing-xor-∧
module 𝟚°   = CommutativeSemiring commutativeSemiring-∧-∨

𝟚-is-set : is-set 𝟚
𝟚-is-set = dec-eq-is-set _≟_

twist-equiv : 𝟚 ≃ 𝟚
twist-equiv = self-inv-equiv not not-involutive

module _ {{_ : UA}} where
    twist : 𝟚 ≡ 𝟚
    twist = ua twist-equiv

xor-not-not : ∀ x y → (not x) xor (not y) ≡ x xor y
xor-not-not 0₂ y = not-involutive y
xor-not-not 1₂ _ = refl

xor-inj₁ : ∀ x {y z} → (x xor y) ≡ (x xor z) → y ≡ z
xor-inj₁ 0₂ = id
xor-inj₁ 1₂ = not-inj

xor-inj₂ : ∀ x {y z} → (y xor x) ≡ (z xor x) → y ≡ z
xor-inj₂ x {y} {z} p = xor-inj₁ x (Xor°.+-comm x y ∙ p ∙ Xor°.+-comm z x)

module Indexed {a} {A : ★ a} where

    infixr 6 _∧°_
    infixr 5 _∨°_ _xor°_

    _∧°_ : Op₂ (A → 𝟚)
    x ∧° y = x ⟨ _∧_ ⟩° y

    _∨°_ : Op₂ (A → 𝟚)
    x ∨° y = x ⟨ _∨_ ⟩° y

    _xor°_ : Op₂ (A → 𝟚)
    x xor° y = x ⟨ _xor_ ⟩° y

    _==°_ : Op₂ (A → 𝟚)
    x ==° y = x ⟨ _==_ ⟩° y

    not° : Op₁ (A → 𝟚)
    not° f = not ∘ f
-- -}
-- -}
-- -}
