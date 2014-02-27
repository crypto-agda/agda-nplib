-- NOTE with-K
module Relation.Binary.PropositionalEquality.K where

open import Type hiding (★)
open import Relation.Binary.PropositionalEquality
{-
open import Data.One using (𝟙)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.Bijection
open import Relation.Binary.Logical
-}
open import Relation.Binary.NP
open import Relation.Nullary

module _ where
  postulate
    Is-set : ∀ {a} → Set a → Set a

proof-irrelevance : ∀ {a} {A : Set a} {A-is-set : Is-set A} {x y : A} (p q : x ≡ y) → p ≡ q
proof-irrelevance refl refl = refl

module _ {a} {A : ★ a} where
  _≡≡_ : ∀ {x y : A} (p q : x ≡ y) → p ≡ q
  _≡≡_ refl refl = refl

  _≟≡_ : ∀ {i j : A} → Decidable {A = i ≡ j} _≡_
  _≟≡_ refl refl = yes refl
