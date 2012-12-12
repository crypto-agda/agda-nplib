module Relation.Unary.NP where

open import Level
open import Type hiding (★)
open import Relation.Unary public hiding (Pred)

-- Flipped version of Relation.Unary.Pred which scale better
-- to logical relation [Pred] and ⟦Pred⟧
Pred : ∀ ℓ {a} (A : ★ a) → ★ (a ⊔ suc ℓ)
Pred ℓ A = A → ★ ℓ
