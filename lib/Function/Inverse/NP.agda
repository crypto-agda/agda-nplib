module Function.Inverse.NP where

open import Function.Inverse public
import Function as F
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary
open import Data.Product
open import Type hiding (★)
open import Relation.Binary.PropositionalEquality using (→-to-⟶)
open import Function.LeftInverse using (_LeftInverseOf_; _RightInverseOf_)

isEquivalence : ∀ {f₁ f₂} → IsEquivalence (Inverse {f₁} {f₂})
isEquivalence = record
   { refl  = id
   ; sym   = sym
   ; trans = F.flip _∘_ }

setoid : ∀ {c ℓ} → Setoid _ _
setoid {c} {ℓ} = record
  { Carrier       = Setoid c ℓ
  ; _≈_           = Inverse
  ; isEquivalence = isEquivalence }

inverses : ∀ {f t}
             {From : ★ f} {To : ★ t}
             (to   : From → To) →
             (from : To → From) →
             (→-to-⟶ from) LeftInverseOf (→-to-⟶ to) →
             (→-to-⟶ from) RightInverseOf (→-to-⟶ to) →
             From ↔ To
inverses to from left right =
  record { inverse-of = inv }
  where inv : →-to-⟶ from InverseOf →-to-⟶ to
        inv = record { left-inverse-of = left ; right-inverse-of = right }

_$₁_ : ∀ {f₁ f₂ t₁ t₂}
         {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
       → Inverse From To → Setoid.Carrier From → Setoid.Carrier To
iso $₁ x = Inverse.to iso ⟨$⟩ x

_$₂_ : ∀ {f₁ f₂ t₁ t₂}
         {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
       → Inverse From To → Setoid.Carrier To → Setoid.Carrier From
iso $₂ x = Inverse.from iso ⟨$⟩ x

_∈_ : ∀ {a₁ a₂}
        {A₁ A₂  : Setoid a₁ a₂}
        (xᵢ     : Setoid.Carrier A₁ × Setoid.Carrier A₂)
        (bij    : Inverse A₁ A₂)
      → ★ a₂
_∈_ {A₂ = A₂} (x₁ , x₂) iso = iso $₁ x₁ ≈ x₂
  where open Setoid A₂
