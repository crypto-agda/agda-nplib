{-# OPTIONS --without-K #-}
module Relation.Binary.PropositionalEquality.K where

open import Level.NP using (ₛ; _⊔_)
open import Type using (★₀; ★_)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; J; refl; !_; tr)
open import Relation.Binary.NP using (Decidable)
open import Relation.Nullary using (yes)
open import Function using (flip)

module _ {a} {A : ★ a} where
    K-Axiom : ★ a
    K-Axiom = ∀ {x : A} (p : x ≡ x) → p ≡ refl

    K-Elim : ∀ {ℓ} → ★(ₛ ℓ ⊔ a)
    K-Elim {ℓ} = {x : A}
                 (P : x ≡ x → ★ ℓ)
                 (P-refl : P refl) (p : x ≡ x) → P p

    UIP-Axiom : ★ a
    UIP-Axiom = ∀ {x y : A} (p q : x ≡ y) → p ≡ q

    K→UIP : K-Axiom → UIP-Axiom
    K→UIP K {x} p q = J (λ y q → (p : x ≡ y) → p ≡ q) K q p

    UIP→K : UIP-Axiom → K-Axiom
    UIP→K UIP p = UIP p refl

    K-Elim→K-Axiom : K-Elim → K-Axiom
    K-Elim→K-Axiom K-elim = K-elim (flip _≡_ refl) refl

    K-Axiom→K-Elim : ∀ {ℓ} → K-Axiom → K-Elim {ℓ}
    K-Axiom→K-Elim K P P-refl p = tr P (! K→UIP K p refl) P-refl

postulate
  KA : ★₀
  K  : ∀ {a} {A : ★ a} {{_ : KA}} {x : A} → (p : x ≡ x) → p ≡ refl

module _ {a} {A : ★ a} {{_ : KA}} {x : A} where
  K-elim : ∀ {ℓ} (P : x ≡ x → ★ ℓ)
             (P-refl : P refl) (p : x ≡ x) → P p
  K-elim = K-Axiom→K-Elim K

  proof-irrelevance : {y : A} (p q : x ≡ y) → p ≡ q
  proof-irrelevance = K→UIP K

  UIP  = proof-irrelevance
  _≡≡_ = proof-irrelevance

  _≟≡_ : ∀ {y : A} → Decidable {A = x ≡ y} _≡_
  _≟≡_ p q = yes (proof-irrelevance p q)

  K-def : K {x = x} refl ≡ refl
  K-def = K (K refl)
-- -}
-- -}
-- -}
