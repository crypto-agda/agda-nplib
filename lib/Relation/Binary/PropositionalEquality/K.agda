module Relation.Binary.PropositionalEquality.K where

open import Type hiding (★)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; J; refl)
open import Relation.Binary.NP using (Decidable)
open import Relation.Nullary using (yes)

postulate
  KA : ★₀

module _ {a} {A : ★ a} {{_ : KA}} where

  K : {x : A} (p : x ≡ x) → p ≡ refl
  K refl = refl

  proof-irrelevance : {x y : A} (p q : x ≡ y) → p ≡ q
  proof-irrelevance {x} p q = J (λ y q → (p : x ≡ y) → p ≡ q) K q p

  _≡≡_ : {x y : A} (p q : x ≡ y) → p ≡ q
  _≡≡_ = proof-irrelevance

  _≟≡_ : ∀ {i j : A} → Decidable {A = i ≡ j} _≡_
  _≟≡_ p q = yes (proof-irrelevance p q)
