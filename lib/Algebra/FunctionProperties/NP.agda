{-# OPTIONS --without-K #-}
-- There is some extensions such as:
-- * interchange
-- * non-zero inversions
-- * cancelation and non-zero cancelation
open import Relation.Nullary
open import Relation.Binary.NP
open import Level.NP
open import Function.NP using (flip; module FromΠ; _$⟨_⟩_; Fun₁; Fun₂; Op₁; Op₂)
open import Data.Product using (_×_; ∃; _,_)
open import Data.Nat.Base using (ℕ)

module Algebra.FunctionProperties.NP
         (Π : ∀ {a b}(A : Set a)(B : A → Set b) → Set(a ⊔ b))
         {a ℓ}{A : Set a}(ℛ : Rel A ℓ) where

open FromΠ Π

private
  infix 0 _≈_ _≉_
  _≈_ : Rel A ℓ
  _≈_ = ℛ

  _≉_ : Rel A ℓ
  x ≉ y = ¬(x ≈ y)

------------------------------------------------------------------------
-- Properties of operations

Associative : Op₂ A → Set _
Associative _·_ = ∀₃ λ x y z → (x · y) · z ≈ x · (y · z)

Associatives : Op₂ A → Set _
Associatives · = Associative · × Associative (flip ·)

Commutative : Op₂ A → Set _
Commutative _·_ = ∀₂ λ x y → x · y ≈ y · x

LeftIdentity : A → Op₂ A → Set _
LeftIdentity e _·_ = ∀₁ λ x → e · x ≈ x

RightIdentity : A → Op₂ A → Set _
RightIdentity e _·_ = ∀₁ λ x → x · e ≈ x

Identity : A → Op₂ A → Set _
Identity e · = LeftIdentity e · × RightIdentity e ·

LeftZero : A → Op₂ A → Set _
LeftZero z _·_ = ∀₁ λ x → z · x ≈ z

RightZero : A → Op₂ A → Set _
RightZero z _·_ = ∀₁ λ x → x · z ≈ z

Zero : A → Op₂ A → Set _
Zero z · = LeftZero z · × RightZero z ·

LeftInverse : A → Op₁ A → Op₂ A → Set _
LeftInverse e _⁻¹ _·_ = ∀₁ λ x → x ⁻¹ · x ≈ e

LeftInverseNonZero : (zero e : A) → Op₁ A → Op₂ A → Set _
LeftInverseNonZero zero e _⁻¹ _·_ = ∀₁ λ x → x ≉ zero → x ⁻¹ · x ≈ e

RightInverse : A → Op₁ A → Op₂ A → Set _
RightInverse e _⁻¹ _·_ = ∀₁ λ x → x · x ⁻¹ ≈ e

RightInverseNonZero : (zero e : A) → Op₁ A → Op₂ A → Set _
RightInverseNonZero zero e _⁻¹ _·_ = ∀₁ λ x → x ≉ zero → x · x ⁻¹ ≈ e

Inverse : A → Op₁ A → Op₂ A → Set _
Inverse e ⁻¹ · = LeftInverse e ⁻¹ · × RightInverse e ⁻¹ ·

InverseNonZero : (zero e : A) → Op₁ A → Op₂ A → Set _
InverseNonZero zero e ⁻¹ · = LeftInverseNonZero zero e ⁻¹ · × RightInverseNonZero zero e ⁻¹ ·

_DistributesOverˡ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverˡ _+_ =
  ∀₃ λ x y z → x * (y + z) ≈ (x * y) + (x * z)

_DistributesOverʳ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverʳ _+_ =
  ∀₃ λ x y z → (y + z) * x ≈ (y * x) + (z * x)

_DistributesOver_ : Op₂ A → Op₂ A → Set _
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)

_IdempotentOn_ : Op₂ A → A → Set _
_·_ IdempotentOn x = x · x ≈ x

Idempotent : Op₂ A → Set _
Idempotent · = ∀₁ λ x → · IdempotentOn x

IdempotentFun : Op₁ A → Set _
IdempotentFun f = ∀₁ λ x → f (f x) ≈ f x

_Absorbs_ : Op₂ A → Op₂ A → Set _
_·_ Absorbs _∘_ = ∀₂ λ x y → x · (x ∘ y) ≈ x

Absorptive : Op₂ A → Op₂ A → Set _
Absorptive · ∘ = (· Absorbs ∘) × (∘ Absorbs ·)

Involutive : Op₁ A → Set _
Involutive f = ∀₁ λ x → f (f x) ≈ x

Interchange : Op₂ A → Op₂ A → Set _
Interchange _·_ _∘_ = ∀₄ λ x y z t → (x · y) ∘ (z · t) ≈ (x ∘ z) · (y ∘ t)

LeftCancel : Op₂ A → Set _
LeftCancel _·_ = ∀₃ λ c x y → c · x ≈ c · y → x ≈ y

RightCancel : Op₂ A → Set _
RightCancel _·_ = ∀₃ λ c x y → x · c ≈ y · c → x ≈ y

LeftCancelNonZero : A → Op₂ A → Set _
LeftCancelNonZero zero _·_ = ∀₃ λ c x y → c ≉ zero → c · x ≈ c · y → x ≈ y

RightCancelNonZero : A → Op₂ A → Set _
RightCancelNonZero zero _·_ = ∀₃ λ c x y → c ≉ zero → x · c ≈ y · c → x ≈ y

module Morphisms {b ℓᴮ}{B : Set b}(_≈ᴮ_ : Rel B ℓᴮ)(⟦_⟧ : A → B) where
  Homomorphic₀ : A → B → Set _
  Homomorphic₀ ∙ ∘ = ⟦ ∙ ⟧ ≈ᴮ ∘

  Homomorphic₁ : Fun₁ A → Op₁ B → Set _
  Homomorphic₁ ∙_ ∘_ = ∀₁ λ x → ⟦ ∙ x ⟧ ≈ᴮ ∘ ⟦ x ⟧

  Homomorphic₂ : Fun₂ A → Op₂ B → Set _
  Homomorphic₂ _∙_ _∘_ =
    ∀₂ λ x y → ⟦ x ∙ y ⟧ ≈ᴮ (⟦ x ⟧ ∘ ⟦ y ⟧)

  Injective : Set _
  Injective = ∀₂ λ x y → ⟦ x ⟧ ≈ᴮ ⟦ y ⟧ → x ≈ y

  Conflict : Set _
  Conflict = ∃ λ x → ∃ λ y → (x ≉ y) × (⟦ x ⟧ ≈ᴮ ⟦ y ⟧)

module EndoMorphisms (⟦_⟧ : A → A) where
  open Morphisms {B = A} _≈_ ⟦_⟧ public

  Cycle^ : ℕ → Set _
  Cycle^ n = ∃ λ x → ⟦_⟧ $⟨ n ⟩ x ≈ x

  Cycle = ∃ Cycle^
-- -}
-- -}
-- -}
-- -}
