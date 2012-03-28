{-# OPTIONS --universe-polymorphism #-}
module Category.Functor.NP where

open import Relation.Binary

Fmap : ∀ {i j ℓ₁ ℓ₂} {I : Set i} {J : Set j}
         (_↝₁_ : Rel I ℓ₁) (_↝₂_ : Rel J ℓ₂) (F : I → J) → Set _
Fmap _↝₁_ _↝₂_ F = ∀ {A B} → A ↝₁ B → F A ↝₂ F B
