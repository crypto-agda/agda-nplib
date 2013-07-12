open import Data.Two

module Data.Two.Logical where

data ⟦𝟚⟧ : (b₁ b₂ : 𝟚) → ★₀ where
  ⟦0₂⟧ : ⟦𝟚⟧ 0₂ 0₂
  ⟦1₂⟧ : ⟦𝟚⟧ 1₂ 1₂

private
 module ⟦𝟚⟧-Internals where
  refl : Reflexive ⟦𝟚⟧
  refl {1₂}   = ⟦1₂⟧
  refl {0₂}  = ⟦0₂⟧

  sym : Symmetric ⟦𝟚⟧
  sym ⟦1₂⟧  = ⟦1₂⟧
  sym ⟦0₂⟧ = ⟦0₂⟧

  trans : Transitive ⟦𝟚⟧
  trans ⟦1₂⟧   = id
  trans ⟦0₂⟧  = id

  subst : ∀ {ℓ} → Substitutive ⟦𝟚⟧ ℓ
  subst _ ⟦1₂⟧   = id
  subst _ ⟦0₂⟧  = id

  _≟_ : Decidable ⟦𝟚⟧
  1₂   ≟  1₂   = yes ⟦1₂⟧
  0₂  ≟  0₂  = yes ⟦0₂⟧
  1₂   ≟  0₂  = no (λ())
  0₂  ≟  1₂   = no (λ())

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
⟦if⟨_⟩_then_else_⟧ _ ⟦1₂⟧  xᵣ _ = xᵣ
⟦if⟨_⟩_then_else_⟧ _ ⟦0₂⟧ _ xᵣ = xᵣ

⟦If′⟨_,_⟩_then_else_⟧ : ∀ {ℓ₁ ℓ₂ ℓᵣ} →
                       (∀⟨ Aᵣ ∶ ⟦★⟧ {ℓ₁} {ℓ₂} ℓᵣ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ {ℓ₁} {ℓ₂} ℓᵣ ⟩⟦→⟧
                           ⟨ bᵣ ∶ ⟦𝟚⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ ⟦if⟨ ⟦★⟧ _ ⟩ bᵣ then Aᵣ else Bᵣ ⟧)
                       If′_then_else_ If′_then_else_
⟦If′⟨_,_⟩_then_else_⟧ _ _ ⟦1₂⟧  xᵣ _ = xᵣ
⟦If′⟨_,_⟩_then_else_⟧ _ _ ⟦0₂⟧ _ xᵣ = xᵣ


⟦not⟧ : (⟦Bool⟧ ⟦→⟧ ⟦Bool⟧) not not
⟦not⟧ ⟦true⟧  = ⟦false⟧
⟦not⟧ ⟦false⟧ = ⟦true⟧

_⟦∧⟧_ : (⟦Bool⟧ ⟦→⟧ ⟦Bool⟧ ⟦→⟧ ⟦Bool⟧) _∧_ _∧_
⟦true⟧  ⟦∧⟧ x = x
⟦false⟧ ⟦∧⟧ _ = ⟦false⟧

_⟦∨⟧_ : (⟦Bool⟧ ⟦→⟧ ⟦Bool⟧ ⟦→⟧ ⟦Bool⟧) _∨_ _∨_
⟦true⟧  ⟦∨⟧ _ = ⟦true⟧
⟦false⟧ ⟦∨⟧ x = x

_⟦xor⟧_ : (⟦Bool⟧ ⟦→⟧ ⟦Bool⟧ ⟦→⟧ ⟦Bool⟧) _xor_ _xor_
⟦true⟧  ⟦xor⟧ x = ⟦not⟧ x
⟦false⟧ ⟦xor⟧ x = x

⟦true⟧′ : ∀ {b} → ✓ b → ⟦Bool⟧ true b
⟦true⟧′ {true}  _ = ⟦true⟧
⟦true⟧′ {false} ()

⟦false⟧′ : ∀ {b} → ✓ (not b) → ⟦Bool⟧ false b
⟦false⟧′ {true} ()
⟦false⟧′ {false} _ = ⟦false⟧

module ⟦Bool⟧-Reasoning = Setoid-Reasoning ⟦Bool⟧-Props.setoid
