module Function.Inverse.NP where

open import Function.Inverse public
open import Function.Equality
open import Relation.Binary
open import Data.Product

_$₁_ : ∀ {f₁ f₂ t₁ t₂}
           {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
         → Inverse From To → Setoid.Carrier From → Setoid.Carrier To
iso $₁ x = Inverse.to iso ⟨$⟩ x

_$₂_ : ∀ {f₁ f₂ t₁ t₂}
           {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
         → Inverse From To → Setoid.Carrier To → Setoid.Carrier From
iso $₂ x = Inverse.from iso ⟨$⟩ x

_∈_ : ∀  {a₁ a₂}
         {A₁ A₂  : Setoid a₁ a₂}
         (xᵢ     : Setoid.Carrier A₁ × Setoid.Carrier A₂)
         (bij    : Inverse A₁ A₂)
      →  Set a₂
_∈_ {A₂ = A₂} (x₁ , x₂) iso = iso $₁ x₁ ≈ x₂
  where open Setoid A₂
