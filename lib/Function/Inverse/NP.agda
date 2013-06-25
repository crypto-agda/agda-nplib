module Function.Inverse.NP where

open import Function.Inverse public
import Function as F
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary
open import Data.Product
open import Type hiding (★)
open import Relation.Binary.PropositionalEquality using (→-to-⟶)
import Function.Equality as FE
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

module _ {a b ra rb}
         {A  : Setoid a ra}
         {B  : Setoid b rb}
  where
  module Aˢ = Setoid A
  module Bˢ = Setoid B
  open Aˢ renaming (_≈_ to _≈ᴬ_)
  open Bˢ renaming (_≈_ to _≈ᴮ_)

  module _ (xᵢ : Setoid.Carrier A × Setoid.Carrier B)
           (f  : Inverse A B)
           where
    x₁ = proj₁ xᵢ
    x₂ = proj₂ xᵢ

    _∈_  : ★ rb
    _∈_  = f $₁ x₁ ≈ᴮ x₂

    _∈′_ : ★ ra
    _∈′_ = x₁ ≈ᴬ f $₂ x₂

  ∈→∈′ : ∀ f xᵢ → xᵢ ∈ f → xᵢ ∈′ f
  ∈→∈′ f (x₁ , x₂) p = Aˢ.trans (Aˢ.sym (Inverse.left-inverse-of f x₁)) (FE.cong (Inverse.from f) p)

  ∈′→∈ : ∀ f xᵢ → xᵢ ∈′ f → xᵢ ∈ f
  ∈′→∈ f (x₁ , x₂) p = Bˢ.trans (FE.cong (Inverse.to f) p) (Inverse.right-inverse-of f x₂)
