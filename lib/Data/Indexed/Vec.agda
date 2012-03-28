{-# OPTIONS --universe-polymorphism #-}
open import Data.Vec
open import Data.Nat
import Data.Indexed

module Data.Indexed.Vec where

open Data.Indexed

|vmap| : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Vec A |↦| Vec B
|vmap| f {n} xs = map f xs
