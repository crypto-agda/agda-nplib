{-# OPTIONS --universe-polymorphism #-}
module Function.Injection.NP where

open import Function.Injection public
open import Function.Equality
open import Relation.Binary
open import Data.Product
open import Level
open import Type hiding (★)

_∈_ : ∀  {a₁ a₂}
         {A₁ A₂  : Setoid a₁ a₂}
         (xᵢ     : Setoid.Carrier A₁ × Setoid.Carrier A₂)
         (inj    : Injection A₁ A₂)
      →  ★ a₂
_∈_ {A₂ = A₂} (x₁ , x₂) inj = Injection.to inj ⟨$⟩ x₁ ≈ x₂
  where open Setoid A₂

