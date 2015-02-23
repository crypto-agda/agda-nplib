{-# OPTIONS --with-K #-}
open import Function
open import Data.Nat hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.NP
open import Relation.Binary.Logical
import Relation.Binary.PropositionalEquality as ≡

module Data.Nat.Logical where

open import Data.Nat.Param.Binary public

_≟_ : Decidable ⟦ℕ⟧
zero  ≟ zero   = yes ⟦zero⟧
suc m ≟ suc n  with m ≟ n
...            | yes p = yes (⟦suc⟧ p)
...            | no ¬p = no (¬p ∘ ⟦pred⟧)
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()

private
  refl : Reflexive ⟦ℕ⟧
  refl {zero}  = ⟦zero⟧
  refl {suc n} = ⟦suc⟧ (refl {n})
  sym : Symmetric ⟦ℕ⟧
  sym ⟦zero⟧ = ⟦zero⟧
  sym (⟦suc⟧ nᵣ) = ⟦suc⟧ (sym nᵣ)
  trans : Transitive ⟦ℕ⟧
  trans ⟦zero⟧    ⟦zero⟧     = ⟦zero⟧
  trans (⟦suc⟧ mᵣ) (⟦suc⟧ nᵣ) = ⟦suc⟧ (trans mᵣ nᵣ)
  subst : ∀ {ℓ} → Substitutive ⟦ℕ⟧ ℓ
  subst _ ⟦zero⟧    = id
  subst P (⟦suc⟧ nᵣ) = subst (P ∘ suc) nᵣ

⟦ℕ⟧-isEquivalence : IsEquivalence ⟦ℕ⟧
⟦ℕ⟧-isEquivalence = record { refl = refl; sym = sym; trans = trans }

⟦ℕ⟧-isDecEquivalence : IsDecEquivalence ⟦ℕ⟧
⟦ℕ⟧-isDecEquivalence = record { isEquivalence = ⟦ℕ⟧-isEquivalence; _≟_ = _≟_ }

⟦ℕ⟧-setoid : Setoid _ _
⟦ℕ⟧-setoid = record { Carrier = ℕ; _≈_ = ⟦ℕ⟧; isEquivalence = ⟦ℕ⟧-isEquivalence }

⟦ℕ⟧-decSetoid : DecSetoid _ _
⟦ℕ⟧-decSetoid = record { Carrier = ℕ; _≈_ = ⟦ℕ⟧; isDecEquivalence = ⟦ℕ⟧-isDecEquivalence }

⟦ℕ⟧-cong : ∀ f → ⟦ℕ⟧ =[ f ]⇒ ⟦ℕ⟧
⟦ℕ⟧-cong _ ⟦zero⟧     = refl
⟦ℕ⟧-cong f (⟦suc⟧ nᵣ) = ⟦ℕ⟧-cong (f ∘ suc) nᵣ

⟦ℕ⟧-equality : Equality ⟦ℕ⟧
⟦ℕ⟧-equality = record { isEquivalence = ⟦ℕ⟧-isEquivalence; subst = subst }

⟦ℕ⟧⇒≡ : ⟦ℕ⟧ ⇒ ≡._≡_
⟦ℕ⟧⇒≡ = Equality.to-reflexive ⟦ℕ⟧-equality {≡._≡_} ≡.refl

module ⟦ℕ⟧ˢ = DecSetoid ⟦ℕ⟧-decSetoid

module ⟦ℕ⟧ᵉ = Equality ⟦ℕ⟧-equality
module ⟦ℕ⟧-Reasoning = Setoid-Reasoning ⟦ℕ⟧-setoid

_⟦≤?⟧_ : ⟦Decidable⟧ ⟦ℕ⟧ ⟦ℕ⟧ ⟦≤⟧ _≤?_ _≤?_
⟦zero⟧             ⟦≤?⟧ _      = yes z≤n
⟦suc⟧ nᵣ           ⟦≤?⟧ ⟦zero⟧   = no (λ())
⟦suc⟧ {m₁} {m₂} mᵣ ⟦≤?⟧ ⟦suc⟧ {n₁} {n₂} nᵣ
 with m₁ ≤? n₁ | m₂ ≤? n₂ | mᵣ ⟦≤?⟧ nᵣ
... | yes _     | yes _      | yes m≤nᵣ = yes (s≤s m≤nᵣ)
... | no _      | no _       | no ¬m≤nᵣ = no (¬m≤nᵣ ∘ ⟦≤-pred⟧)
... | yes _     | no _       | ()
... | no _      | yes _      | ()
-- -}
