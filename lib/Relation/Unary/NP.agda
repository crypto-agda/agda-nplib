{-# OPTIONS --without-K #-}
module Relation.Unary.NP where

open import Level
open import Relation.Unary public hiding (Pred)

-- Flipped version of Relation.Unary.Pred which scale better
-- to logical relation [Pred] and ⟦Pred⟧
Pred : ∀ ℓ {a} (A : Set a) → Set (a ⊔ suc ℓ)
Pred ℓ A = A → Set ℓ
