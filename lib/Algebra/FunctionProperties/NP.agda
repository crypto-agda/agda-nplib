open import Relation.Binary.NP
open import Type hiding (★)
import Algebra.FunctionProperties

module Algebra.FunctionProperties.NP {a ℓ} {A : ★ a} (_≈_ : Rel A ℓ) where

open Algebra.FunctionProperties _≈_ public

Interchange : Op₂ A → Op₂ A → ★ _
Interchange _∙_ _∘_ = ∀ x y z t → ((x ∙ y) ∘ (z ∙ t)) ≈ ((x ∘ z) ∙ (y ∘ t))

module InterchangeFromAssocCommCong
         (isEquivalence : IsEquivalence _≈_)
         (_∙_ : Op₂ A)
         (∙-assoc : Associative _∙_)
         (∙-comm : Commutative _∙_)
         (∙-cong : ∀ {x y} z → x ≈ y → (x ∙ z) ≈ (y ∙ z))
         where

    open IsEquivalence isEquivalence
    open Equivalence-Reasoning isEquivalence

    ∙-cong′ : ∀ x {y z} → y ≈ z → (x ∙ y) ≈ (x ∙ z)
    ∙-cong′ x {y} {z} y≈z = x ∙ y
                          ≈⟨ ∙-comm _ _ ⟩
                            y ∙ x
                          ≈⟨ ∙-cong x y≈z ⟩
                            z ∙ x
                          ≈⟨ ∙-comm _ _ ⟩
                            x ∙ z
                          ∎

    ∙-interchange : Interchange _∙_ _∙_
    ∙-interchange x y z t
                = (x ∙ y) ∙ (z ∙ t)
                ≈⟨ ∙-assoc x y _ ⟩
                  x ∙ (y ∙ (z ∙ t))
                ≈⟨ ∙-cong′ x (sym (∙-assoc y z t)) ⟩
                  x ∙ ((y ∙ z) ∙ t)
                ≈⟨ ∙-cong′ x (∙-cong t (∙-comm _ _)) ⟩
                  x ∙ ((z ∙ y) ∙ t)
                ≈⟨ ∙-cong′ x (∙-assoc z y t) ⟩
                  x ∙ (z ∙ (y ∙ t))
                ≈⟨ sym (∙-assoc x z _) ⟩
                  (x ∙ z) ∙ (y ∙ t)
                ∎
