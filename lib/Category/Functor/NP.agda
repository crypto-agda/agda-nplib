{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.NP where

open import Type
open import Relation.Binary

Fmap : ∀ {i j ℓ₁ ℓ₂} {I : ★ i} {J : ★ j}
         (_↝₁_ : Rel I ℓ₁) (_↝₂_ : Rel J ℓ₂) (F : I → J) → ★ _
Fmap _↝₁_ _↝₂_ F = ∀ {A B} → A ↝₁ B → F A ↝₂ F B
