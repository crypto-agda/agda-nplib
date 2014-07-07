open import Data.String using (String)
open import Relation.Binary.PropositionalEquality

module Opaque {a} {A : Set a} where

{-
abstract
  opaque : String → A → A
  opaque _ = λ x → x

  opaque-rule : ∀ {s} x → opaque s x ≡ x
  opaque-rule x = refl
-}

postulate
  opaque : String → A → A
  opaque-rule : ∀ {s} x → opaque s x ≡ x
