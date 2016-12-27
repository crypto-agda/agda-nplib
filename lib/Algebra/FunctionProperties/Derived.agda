{-# OPTIONS --without-K #-}
open import Relation.Binary.NP
open import Function.NP using (Π; Op₂)
open import Type using () renaming (Type_ to Type)

module Algebra.FunctionProperties.Derived {a ℓ} {A : Type a} (_≈_ : Rel A ℓ) where

open import Algebra.FunctionProperties.NP Π _≈_

module FromAssocCommCong
         (isEquivalence : IsEquivalence _≈_)
         (op : Op₂ A)
         (∙-assoc : Associative op)
         (∙-comm : Commutative op)
         (∙-cong : ∀ {x y} z → x ≈ y → op x z ≈ op y z)
         where

    infix 6 _∙_
    private
      _∙_ : Op₂ A
      _∙_ = op

    open IsEquivalence isEquivalence
    open Equivalence-Reasoning isEquivalence

    ∙-cong′ : ∀ x {y z} → y ≈ z → (x ∙ y) ≈ (x ∙ z)
    ∙-cong′ x {y} {z} y≈z
      = x ∙ y  ≈⟨ ∙-comm _ _ ⟩
        y ∙ x  ≈⟨ ∙-cong x y≈z ⟩
        z ∙ x  ≈⟨ ∙-comm _ _ ⟩
        x ∙ z  ∎

    interchange : Interchange _∙_ _∙_
    interchange x y z t
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
