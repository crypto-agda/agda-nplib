{-# OPTIONS --without-K #-}
module Relation.Binary.PropositionalEquality.NP where

open import Relation.Binary.PropositionalEquality
  public
  hiding (_≗_; module ≡-Reasoning)

open import Relation.Binary.PropositionalEquality.Base
  public

open import Function.Param.Binary
open import Type.Param.Binary

data ⟦≡⟧ {a₀ a₁ aᵣ}
         {A₀ A₁} (Aᵣ : ⟦★⟧ {a₀} {a₁} aᵣ A₀ A₁)
         {x₀ x₁} (xᵣ : Aᵣ x₀ x₁)
       : (Aᵣ ⟦→⟧ ⟦★⟧ aᵣ) (_≡_ x₀) (_≡_ x₁) where
    -- : ∀ {y₀ y₁} (yᵣ : Aᵣ y₀ y₁) → x₀ ≡ y₀ → x₁ ≡ y₁ → ★
  ⟦refl⟧ : ⟦≡⟧ Aᵣ xᵣ xᵣ refl refl

-- Double checking level 0 with a direct ⟦_⟧ encoding
private
  ⟦≡⟧′ : (∀⟨ Aᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ ⟦★₀⟧) _≡_ _≡_
  ⟦≡⟧′ = ⟦≡⟧

  ⟦refl⟧′ : (∀⟨ Aᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ ∀⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ ⟦≡⟧ Aᵣ xᵣ xᵣ) refl refl
  ⟦refl⟧′ _ _ = ⟦refl⟧
