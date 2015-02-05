open import Data.String using (String)
open import Relation.Binary.PropositionalEquality

module Opaque {a b} {A : Set a} {B : Set b} where

{-
abstract
  opaque : A → B → B
  opaque _ = λ x → x

  opaque-rule : ∀ {x} y → opaque x y ≡ y
  opaque-rule _ = refl
-}

postulate
  opaque : A → B → B
  opaque-rule : ∀ {x} y → opaque x y ≡ y
