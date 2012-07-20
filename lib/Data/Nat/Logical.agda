{-# OPTIONS --universe-polymorphism #-}
module Data.Nat.Logical where

import Level as L
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; z≤n; s≤s; ≤-pred; _≤?_; _+_)
open import Function
open import Relation.Nullary
open import Relation.Binary.NP
open import Relation.Binary.Logical
import      Relation.Binary.PropositionalEquality as PropEq

data ⟦ℕ⟧ : ⟦Set₀⟧ ℕ ℕ where
  zero : ⟦ℕ⟧ zero zero
  suc  : ∀ {n₁ n₂} (nᵣ : ⟦ℕ⟧ n₁ n₂) → ⟦ℕ⟧ (suc n₁) (suc n₂)

_⟦+⟧_ : (⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧) _+_ _+_
zero  ⟦+⟧ n = n
suc m ⟦+⟧ n = suc (m ⟦+⟧ n)

⟦pred⟧ : (⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧) pred pred
⟦pred⟧ (suc nᵣ) = nᵣ
⟦pred⟧ zero     = zero

_≟_ : Decidable ⟦ℕ⟧
zero  ≟ zero   = yes zero
suc m ≟ suc n  with m ≟ n
...            | yes p = yes (suc p)
...            | no ¬p = no (¬p ∘ ⟦pred⟧)
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()

private
  refl : Reflexive ⟦ℕ⟧
  refl {zero}  = zero
  refl {suc n} = suc (refl {n})
  sym : Symmetric ⟦ℕ⟧
  sym zero = zero
  sym (suc nᵣ) = suc (sym nᵣ)
  trans : Transitive ⟦ℕ⟧
  trans zero    zero     = zero
  trans (suc mᵣ) (suc nᵣ) = suc (trans mᵣ nᵣ)
  subst : ∀ {ℓ} → Substitutive ⟦ℕ⟧ ℓ
  subst _ zero    = id
  subst P (suc nᵣ) = subst (P ∘ suc) nᵣ

⟦ℕ⟧-isEquivalence : IsEquivalence ⟦ℕ⟧
⟦ℕ⟧-isEquivalence = record { refl = refl; sym = sym; trans = trans }

⟦ℕ⟧-isDecEquivalence : IsDecEquivalence ⟦ℕ⟧
⟦ℕ⟧-isDecEquivalence = record { isEquivalence = ⟦ℕ⟧-isEquivalence; _≟_ = _≟_ }

⟦ℕ⟧-equality : Equality ⟦ℕ⟧
⟦ℕ⟧-equality = record { isEquivalence = ⟦ℕ⟧-isEquivalence; subst = subst }

⟦ℕ⟧⇒≡ : ⟦ℕ⟧ ⇒ PropEq._≡_
⟦ℕ⟧⇒≡ = Equality.to-reflexive ⟦ℕ⟧-equality {PropEq._≡_} PropEq.refl

⟦ℕ⟧-setoid : Setoid _ _
⟦ℕ⟧-setoid = record { Carrier = ℕ; _≈_ = ⟦ℕ⟧; isEquivalence = ⟦ℕ⟧-isEquivalence }

⟦ℕ⟧-decSetoid : DecSetoid _ _
⟦ℕ⟧-decSetoid = record { Carrier = ℕ; _≈_ = ⟦ℕ⟧; isDecEquivalence = ⟦ℕ⟧-isDecEquivalence }

⟦ℕ⟧-cong : ∀ f → ⟦ℕ⟧ =[ f ]⇒ ⟦ℕ⟧
⟦ℕ⟧-cong _ zero     = refl
⟦ℕ⟧-cong f (suc nᵣ) = ⟦ℕ⟧-cong (f ∘ suc) nᵣ

module ⟦ℕ⟧ᵉ = Equality ⟦ℕ⟧-equality
module ⟦ℕ⟧ˢ = DecSetoid ⟦ℕ⟧-decSetoid
module ⟦ℕ⟧-Reasoning = Setoid-Reasoning ⟦ℕ⟧-setoid

data ⟦≤⟧ : ⟦REL⟧ ⟦ℕ⟧ ⟦ℕ⟧ L.zero _≤_ _≤_ where
  z≤n : ∀ {m₁ m₂} {mᵣ : ⟦ℕ⟧ m₁ m₂} → ⟦≤⟧ zero mᵣ z≤n z≤n
  s≤s : ∀ {m₁ m₂ n₁ n₂ mᵣ nᵣ} {m≤n₁ : m₁ ≤ n₁} {m≤n₂ : m₂ ≤ n₂} (m≤nᵣ : ⟦≤⟧ mᵣ nᵣ m≤n₁ m≤n₂)
        → ⟦≤⟧ (suc mᵣ) (suc nᵣ) (s≤s m≤n₁) (s≤s m≤n₂)

⟦≤-pred⟧ : ∀ {m₁ m₂ n₁ n₂ mᵣ nᵣ} {m≤n₁ : suc m₁ ≤ suc n₁} {m≤n₂ : suc m₂ ≤ suc n₂}
          → ⟦≤⟧ (suc mᵣ) (suc nᵣ) m≤n₁ m≤n₂ → ⟦≤⟧ mᵣ nᵣ (≤-pred m≤n₁) (≤-pred m≤n₂)
⟦≤-pred⟧ (s≤s m≤n) = m≤n

_⟦≤?⟧_ : ⟦Decidable⟧ ⟦ℕ⟧ ⟦ℕ⟧ ⟦≤⟧ _≤?_ _≤?_
zero             ⟦≤?⟧ _      = yes z≤n
suc nᵣ           ⟦≤?⟧ zero   = no (λ())
suc {m₁} {m₂} mᵣ ⟦≤?⟧ suc {n₁} {n₂} nᵣ
 with m₁ ≤? n₁ | m₂ ≤? n₂ | mᵣ ⟦≤?⟧ nᵣ
... | yes _     | yes _      | yes m≤nᵣ = yes (s≤s m≤nᵣ)
... | no _      | no _       | no ¬m≤nᵣ = no (¬m≤nᵣ ∘ ⟦≤-pred⟧)
... | yes _     | no _       | ()
... | no _      | yes _      | ()
