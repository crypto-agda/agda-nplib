-- NOTE with-K
module Data.Fin.Logical where

open import Function
open import Data.Fin
open import Data.Nat.Logical
open import Relation.Binary
open import Relation.Binary.Logical

private
  module ⟦ℕ⟧s = Setoid ⟦ℕ⟧-setoid

data ⟦Fin⟧ : (⟦ℕ⟧ ⟦→⟧ ⟦★₀⟧) Fin Fin where
  ⟦zero⟧ : ∀ {n₁ n₂} {nᵣ : ⟦ℕ⟧ n₁ n₂} → ⟦Fin⟧ (suc nᵣ) zero zero
  ⟦suc⟧  : ∀ {n₁ n₂} {nᵣ : ⟦ℕ⟧ n₁ n₂} {x₁ x₂} (xᵣ : ⟦Fin⟧ nᵣ x₁ x₂) → ⟦Fin⟧ (suc nᵣ) (suc x₁) (suc x₂)

private
  refl : ∀ {n} → Reflexive (⟦Fin⟧ {n} ⟦ℕ⟧s.refl)
  refl {x = zero}  = ⟦zero⟧
  refl {x = suc _} = ⟦suc⟧ refl

  sym : ∀ {n} → Symmetric (⟦Fin⟧ {n} ⟦ℕ⟧s.refl)
  sym ⟦zero⟧ = ⟦zero⟧
  sym (⟦suc⟧ xᵣ) = ⟦suc⟧ (sym xᵣ)

  trans : ∀ {n} → Transitive (⟦Fin⟧ {n} ⟦ℕ⟧s.refl)
  trans ⟦zero⟧ xᵣ = xᵣ
  trans (⟦suc⟧ xᵣ) (⟦suc⟧ yᵣ) = ⟦suc⟧ (trans xᵣ yᵣ)

  subst : ∀ {ℓ n} → Substitutive (⟦Fin⟧ {n} ⟦ℕ⟧s.refl) ℓ
  subst _ ⟦zero⟧    = id
  subst P (⟦suc⟧ xᵣ) = subst (P ∘ suc) xᵣ

  isEquivalence : ∀ {n} → IsEquivalence (⟦Fin⟧ {n} ⟦ℕ⟧s.refl)
  isEquivalence = record { refl = refl; sym = sym; trans = trans }
