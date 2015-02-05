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

open import Algebra                    using (module CommutativeRing; module CommutativeSemiring)
open import Algebra.FunctionProperties using (Op₁; Op₂)

open import Data.Nat     using (ℕ; _≤_; z≤n; s≤s; _⊓_; _⊔_; _∸_)
open import Data.Zero    using (𝟘-elim)
open import Data.One     using (𝟙)
open import Data.Product using (uncurry; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum     using (_⊎_; inj₁; inj₂)

open import Function.Equivalence using (module Equivalence)
open import Function.Equality    using (_⟨$⟩_)
open import Function.NP          using (id; _∘_; _⟨_⟩°_; flip)

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≢_; refl; idp; _∙_; !_; coe; coe!; J; J-orig)
open import Relation.Nullary                         using (¬_; Dec; yes; no)

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

✓dec : ∀ b → Dec (✓ b)
✓dec = [0: no (λ())
        1: yes _ ]

de-morgan : ∀ x y → not (x ∨ y) ≡ not x ∧ not y
de-morgan 0₂ _ = refl
de-morgan 1₂ _ = refl

≢0→≡1 : ∀ {x} → x ≢ 0₂ → x ≡ 1₂
≢0→≡1 {1₂} p = refl
≢0→≡1 {0₂} p = 𝟘-elim (p refl)

≢1→≡0 : ∀ {x} → x ≢ 1₂ → x ≡ 0₂
≢1→≡0 {0₂} p = refl
≢1→≡0 {1₂} p = 𝟘-elim (p refl)

-- 0₂ is 0 and 1₂ is 1
𝟚▹ℕ : 𝟚 → ℕ
𝟚▹ℕ = [0: 0
       1: 1 ]

𝟚▹ℕ≤1 : ∀ b → 𝟚▹ℕ b ≤ 1
𝟚▹ℕ≤1 = [0: z≤n
         1: s≤s z≤n ]

𝟚▹ℕ-⊓ : ∀ a b → 𝟚▹ℕ a ⊓ 𝟚▹ℕ b ≡ 𝟚▹ℕ (a ∧ b)
𝟚▹ℕ-⊓ 1₂ 0₂ = refl
𝟚▹ℕ-⊓ 1₂ 1₂ = refl
𝟚▹ℕ-⊓ 0₂ _  = refl

𝟚▹ℕ-⊔ : ∀ a b → 𝟚▹ℕ a ⊔ 𝟚▹ℕ b ≡ 𝟚▹ℕ (a ∨ b)
𝟚▹ℕ-⊔ 1₂ 0₂ = refl
𝟚▹ℕ-⊔ 1₂ 1₂ = refl
𝟚▹ℕ-⊔ 0₂ _  = refl

𝟚▹ℕ-∸ : ∀ a b → 𝟚▹ℕ a ∸ 𝟚▹ℕ b ≡ 𝟚▹ℕ (a ∧ not b)
𝟚▹ℕ-∸ 0₂ 0₂ = refl
𝟚▹ℕ-∸ 0₂ 1₂ = refl
𝟚▹ℕ-∸ 1₂ 0₂ = refl
𝟚▹ℕ-∸ 1₂ 1₂ = refl

xor-not-not : ∀ x y → (not x) xor (not y) ≡ x xor y
xor-not-not 0₂ y = not-involutive y
xor-not-not 1₂ _ = refl

not-inj : ∀ {x y} → not x ≡ not y → x ≡ y
not-inj {0₂} {0₂} _ = refl
not-inj {1₂} {1₂} _ = refl
not-inj {0₂} {1₂} ()
not-inj {1₂} {0₂} ()

xor-inj₁ : ∀ x {y z} → (x xor y) ≡ (x xor z) → y ≡ z
xor-inj₁ 0₂ = id
xor-inj₁ 1₂ = not-inj

xor-inj₂ : ∀ x {y z} → (y xor x) ≡ (z xor x) → y ≡ z
xor-inj₂ x {y} {z} p = xor-inj₁ x (Xor°.+-comm x y ∙ p ∙ Xor°.+-comm z x)

module Indexed {a} {A : ★ a} where
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
