{-# OPTIONS --universe-polymorphism #-}
module Function.Bijection.NP where

open import Function.Bijection public
open import Function.Surjection
open import Function.Equality
open import Relation.Binary
open import Data.Product
open import Level

_⟨$⟩₁_ : ∀ {f₁ f₂ t₁ t₂}
           {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
         → Bijection From To → Setoid.Carrier From → Setoid.Carrier To
_⟨$⟩₁_ bij x = Bijection.to bij ⟨$⟩ x

_⟨$⟩₂_ : ∀ {f₁ f₂ t₁ t₂}
           {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
         → Bijection From To → Setoid.Carrier To → Setoid.Carrier From
_⟨$⟩₂_ bij x = Bijection.from bij ⟨$⟩ x

_∈_ : ∀  {a₁ a₂}
         {A₁ A₂  : Setoid a₁ a₂}
         (xᵢ     : Setoid.Carrier A₁ × Setoid.Carrier A₂)
         (bij    : Bijection A₁ A₂)
      →  Set a₂
_∈_ {A₂ = A₂} (x₁ , x₂) bij = bij ⟨$⟩₁ x₁ ≈ x₂
  where open Setoid A₂

-- Bijection is symmetric
flip : ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
       → Bijection From To → Bijection To From
flip bij =
  record { to = from
         ; bijective =
             record { injective = Surjection.injective surjection
                    ; surjective =
                        record { from = to
                               ; right-inverse-of = left-inverse-of } } }
  where open Bijection bij

{-
wip : ∀  {a₁ a₂}
         {A₁ A₂  : Setoid a₁ a₂}
         (xᵢ     : Setoid.Carrier A₁ × Setoid.Carrier A₂)
         (bij    : Bijection A₁ A₂)
      → xᵢ ∈ bij → swap xᵢ ∈ flip bij
wip (x₁ , x₂) bij x = ?
-}
