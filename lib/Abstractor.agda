{-# OPTIONS --universe-polymorphism #-}
module Abstractor where

open import Level

abstract
  abstractor : ∀ {a} {A : Set a} → A → A
  abstractor x = x

