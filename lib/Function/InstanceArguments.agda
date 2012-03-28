{-# OPTIONS --universe-polymorphism #-}

open import Level

module Function.InstanceArguments where

explicitize : ∀ {a b} {A : Set a} {B : A → Set b} →
                (⦃ x : A ⦄ → B x) → (x : A) → B x
explicitize f x = f ⦃ x ⦄

… : ∀ {a} {A : Set a} ⦃ x : A ⦄ → A
… ⦃ x ⦄ = x

