module Relation.Nullary.NP where

open import Type
open import Data.Sum
open import Relation.Nullary public

module _ {a b} {A : ★_ a} {B : ★_ b} where
    Dec-⊎ : Dec A → Dec B → Dec (A ⊎ B)
    Dec-⊎ (yes p) _       = yes (inj₁ p)
    Dec-⊎ (no ¬p) (yes p) = yes (inj₂ p)
    Dec-⊎ (no ¬p) (no ¬q) = no [ ¬p , ¬q ]

    module _ (to : A → B)(from : B → A) where

      map-Dec : Dec A → Dec B
      map-Dec (yes p) = yes (to p)
      map-Dec (no ¬p) = no (λ z → ¬p (from z))
