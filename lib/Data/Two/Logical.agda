module Data.Two.Logical where

open import Data.Two.Param.Binary

open import Function
open import Data.Two hiding (_≟_; decSetoid)
open import Data.Bool using (if_then_else_)
open import Data.Bool.NP using (If′_then_else_)
open import Relation.Nullary
open import Relation.Binary.NP
open import Relation.Binary.Logical

private
 module ⟦𝟚⟧-Internals where
  refl : Reflexive ⟦𝟚⟧
  refl {0₂} = ⟦0₂⟧
  refl {1₂} = ⟦1₂⟧

  sym : Symmetric ⟦𝟚⟧
  sym ⟦0₂⟧ = ⟦0₂⟧
  sym ⟦1₂⟧ = ⟦1₂⟧

  trans : Transitive ⟦𝟚⟧
  trans ⟦0₂⟧ = id
  trans ⟦1₂⟧ = id

  subst : ∀ {ℓ} → Substitutive ⟦𝟚⟧ ℓ
  subst _ ⟦0₂⟧ = id
  subst _ ⟦1₂⟧ = id

  _≟_ : Decidable ⟦𝟚⟧
  0₂ ≟ 0₂ = yes ⟦0₂⟧
  1₂ ≟ 1₂ = yes ⟦1₂⟧
  1₂ ≟ 0₂ = no (λ())
  0₂ ≟ 1₂ = no (λ())

  isEquivalence : IsEquivalence ⟦𝟚⟧
  isEquivalence = record { refl = refl; sym = sym; trans = trans }

  isDecEquivalence : IsDecEquivalence ⟦𝟚⟧
  isDecEquivalence = record { isEquivalence = isEquivalence; _≟_ = _≟_ }

  setoid : Setoid _ _
  setoid = record { Carrier = 𝟚; _≈_ = ⟦𝟚⟧; isEquivalence = isEquivalence }

  decSetoid : DecSetoid _ _
  decSetoid = record { Carrier = 𝟚; _≈_ = ⟦𝟚⟧; isDecEquivalence = isDecEquivalence }

  equality : Equality ⟦𝟚⟧
  equality = record { isEquivalence = isEquivalence; subst = subst }

module ⟦𝟚⟧-Props where
  open ⟦𝟚⟧-Internals public using (subst; decSetoid; equality)
  open DecSetoid decSetoid public
  open Equality equality public hiding (subst; isEquivalence; refl; reflexive; sym; trans)

⟦if⟨_⟩_then_else_⟧ : ∀ {a₁ a₂ aᵣ} → (∀⟨ Aᵣ ∶ ⟦★⟧ {a₁} {a₂} aᵣ ⟩⟦→⟧ ⟦𝟚⟧ ⟦→⟧ Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ Aᵣ) if_then_else_ if_then_else_
⟦if⟨_⟩_then_else_⟧ _ ⟦1₂⟧ xᵣ _  = xᵣ
⟦if⟨_⟩_then_else_⟧ _ ⟦0₂⟧ _  xᵣ = xᵣ

⟦If′⟨_,_⟩_then_else_⟧ : ∀ {ℓ₁ ℓ₂ ℓᵣ} →
                       (∀⟨ Aᵣ ∶ ⟦★⟧ {ℓ₁} {ℓ₂} ℓᵣ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ {ℓ₁} {ℓ₂} ℓᵣ ⟩⟦→⟧
                           ⟨ bᵣ ∶ ⟦𝟚⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ ⟦if⟨ ⟦★⟧ _ ⟩ bᵣ then Aᵣ else Bᵣ ⟧)
                       If′_then_else_ If′_then_else_
⟦If′⟨_,_⟩_then_else_⟧ _ _ ⟦1₂⟧  xᵣ _ = xᵣ
⟦If′⟨_,_⟩_then_else_⟧ _ _ ⟦0₂⟧ _ xᵣ = xᵣ

⟦1₂⟧′ : ∀ {b} → ✓ b → ⟦𝟚⟧ 1₂ b
⟦1₂⟧′ {1₂} _ = ⟦1₂⟧
⟦1₂⟧′ {0₂} ()

⟦0₂⟧′ : ∀ {b} → ✓ (not b) → ⟦𝟚⟧ 0₂ b
⟦0₂⟧′ {1₂} ()
⟦0₂⟧′ {0₂} _ = ⟦0₂⟧

module ⟦𝟚⟧-Reasoning = Setoid-Reasoning ⟦𝟚⟧-Props.setoid
