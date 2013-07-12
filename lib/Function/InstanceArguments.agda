{-# OPTIONS --without-K #-}
open import Level
open import Type hiding (★)

module Function.InstanceArguments where

explicitize : ∀ {a b} {A : ★ a} {B : A → ★ b} →
                (⦃ x : A ⦄ → B x) → (x : A) → B x
explicitize f x = f ⦃ x ⦄

… : ∀ {a} {A : ★ a} ⦃ x : A ⦄ → A
… ⦃ x ⦄ = x

