-- Why I don't want LEM

open import Type
open import Function
open import Data.Two
open import Relation.Binary.Logical
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP

module Relation.Binary.Logical.LEM
  (LEM : (P : ★₁) → Dec P) where

broken-id : ∀ (A : ★) → A → A
broken-id A with LEM (A ≡ 𝟚)
... | yes p = coe! p ∘ not ∘ coe p
... | no ¬p = id
