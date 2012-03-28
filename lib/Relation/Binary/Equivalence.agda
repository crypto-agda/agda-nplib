{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.Equivalence where

open import Level
open import Function
open import Relation.Binary

record Equivalent {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
                  (From : REL A B ℓ₁) (To : REL A B ℓ₂) : Set (ℓ₁ ⊔ ℓ₂ ⊔ a ⊔ b) where
  field
    to   : From ⇒ To
    from : To ⇒ From

infix 2 _⇔_
_⇔_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} (R₁ : REL A B ℓ₁) (R₂ : REL A B ℓ₂) → Set _
_⇔_ = Equivalent

equivalent : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {R₁ : REL A B ℓ₁} {R₂ : REL A B ℓ₂} →
               (R₁ ⇒ R₂) → (R₂ ⇒ R₁) → R₁ ⇔ R₂
equivalent pf⇒ pf⇐ = record { to = λ {x y} → pf⇒ ; from = λ {x y} → pf⇐ }
