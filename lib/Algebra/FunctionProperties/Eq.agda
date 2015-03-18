{-# OPTIONS --without-K #-}
-- Like Algebra.FunctionProperties but specialized to _≡_ and using implict arguments
-- Moreover there is some extensions such as:
-- * interchange
-- * non-zero inversions
-- * cancelation and non-zero cancelation

-- These properties can (for instance) be used to define algebraic
-- structures.

open import Level
open import Function.NP using (_$⟨_⟩_; flip)
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.NP
open import Relation.Binary.PropositionalEquality.NP

-- The properties are specified using the following relation as
-- "equality".

module Algebra.FunctionProperties.Eq {a} {A : Set a} where

------------------------------------------------------------------------
-- Unary and binary operations

open import Algebra.FunctionProperties.Core public

------------------------------------------------------------------------
-- Properties of operations

Associative : Op₂ A → Set _
Associative _·_ = ∀ {x y z} → ((x · y) · z) ≡ (x · (y · z))

Commutative : Op₂ A → Set _
Commutative _·_ = ∀ {x y} → (x · y) ≡ (y · x)

LeftIdentity : A → Op₂ A → Set _
LeftIdentity e _·_ = ∀ {x} → (e · x) ≡ x

RightIdentity : A → Op₂ A → Set _
RightIdentity e _·_ = ∀ {x} → (x · e) ≡ x

Identity : A → Op₂ A → Set _
Identity e · = LeftIdentity e · × RightIdentity e ·

LeftZero : A → Op₂ A → Set _
LeftZero z _·_ = ∀ {x} → (z · x) ≡ z

RightZero : A → Op₂ A → Set _
RightZero z _·_ = ∀ {x} → (x · z) ≡ z

Zero : A → Op₂ A → Set _
Zero z · = LeftZero z · × RightZero z ·

LeftInverse : A → Op₁ A → Op₂ A → Set _
LeftInverse e _⁻¹ _·_ = ∀ {x} → (x ⁻¹ · x) ≡ e

LeftInverseNonZero : (zero e : A) → Op₁ A → Op₂ A → Set _
LeftInverseNonZero zero e _⁻¹ _·_ = ∀ {x} → x ≢ zero → (x ⁻¹ · x) ≡ e

RightInverse : A → Op₁ A → Op₂ A → Set _
RightInverse e _⁻¹ _·_ = ∀ {x} → (x · (x ⁻¹)) ≡ e

RightInverseNonZero : (zero e : A) → Op₁ A → Op₂ A → Set _
RightInverseNonZero zero e _⁻¹ _·_ = ∀ {x} → x ≢ zero → (x · (x ⁻¹)) ≡ e

Inverse : A → Op₁ A → Op₂ A → Set _
Inverse e ⁻¹ · = LeftInverse e ⁻¹ · × RightInverse e ⁻¹ ·

InverseNonZero : (zero e : A) → Op₁ A → Op₂ A → Set _
InverseNonZero zero e ⁻¹ · = LeftInverse e ⁻¹ · × RightInverse e ⁻¹ ·

_DistributesOverˡ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverˡ _+_ =
  ∀ {x y z} → (x * (y + z)) ≡ ((x * y) + (x * z))

_DistributesOverʳ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverʳ _+_ =
  ∀ {x y z} → ((y + z) * x) ≡ ((y * x) + (z * x))

_DistributesOver_ : Op₂ A → Op₂ A → Set _
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)

_IdempotentOn_ : Op₂ A → A → Set _
_·_ IdempotentOn x = (x · x) ≡ x

Idempotent : Op₂ A → Set _
Idempotent · = ∀ {x} → · IdempotentOn x

IdempotentFun : Op₁ A → Set _
IdempotentFun f = ∀ {x} → f (f x) ≡ f x

_Absorbs_ : Op₂ A → Op₂ A → Set _
_·_ Absorbs _∘_ = ∀ {x y} → (x · (x ∘ y)) ≡ x

Absorptive : Op₂ A → Op₂ A → Set _
Absorptive · ∘ = (· Absorbs ∘) × (∘ Absorbs ·)

Involutive : Op₁ A → Set _
Involutive f = ∀ {x} → f (f x) ≡ x

Interchange : Op₂ A → Op₂ A → Set _
Interchange _·_ _∘_ = ∀ {x y z t} → ((x · y) ∘ (z · t)) ≡ ((x ∘ z) · (y ∘ t))

LeftCancel : Op₂ A → Set _
LeftCancel _·_ = ∀ {c x y} → c · x ≡ c · y → x ≡ y

RightCancel : Op₂ A → Set _
RightCancel _·_ = ∀ {c x y} → x · c ≡ y · c → x ≡ y

LeftCancelNonZero : A → Op₂ A → Set _
LeftCancelNonZero zero _·_ = ∀ {c x y} → c ≢ zero → c · x ≡ c · y → x ≡ y

RightCancelNonZero : A → Op₂ A → Set _
RightCancelNonZero zero _·_ = ∀ {c x y} → c ≢ zero → x · c ≡ y · c → x ≡ y

module FromOp₂
         (_·_ : Op₂ A){x x' y y'}(p : x ≡ x')(q : y ≡ y')
       where
  op= : x · y ≡ x' · y'
  op= = ap (_·_ x) q ∙ ap (λ z → z · y') p

module FromComm
         (_·_   : Op₂ A)
         (comm  : Commutative _·_)
         {x y x' y' : A}
         (e : (y · x) ≡ (y' · x'))
       where
  open FromOp₂ _·_

  comm= : x · y ≡ x' · y'
  comm= = comm ∙ e ∙ comm

module FromAssoc
         (_·_   : Op₂ A)
         (assoc : Associative _·_)

       where
  open FromOp₂ _·_

  assocs : Associative _·_ × Associative (flip _·_)
  assocs = assoc , ! assoc

  module _ {c x y x' y' : A}
           (e : (x · y) ≡ (x' · y')) where
    assoc= : x · (y · c) ≡ x' · (y' · c)
    assoc= = ! assoc ∙ op= e idp ∙ assoc

    !assoc= : (c · x) · y ≡ (c · x') · y'
    !assoc= = assoc ∙ op= idp e ∙ ! assoc

  module _ {c d x y x' y' : A}
           (e : (x · y) ≡ (x' · y')) where
    inner= : (c · x) · (y · d) ≡ (c · x') · (y' · d)
    inner= = assoc= (!assoc= e)

module FromAssocComm
         (_·_   : Op₂ A)
         (assoc : Associative _·_)
         (comm  : Commutative _·_)
       where
  open FromOp₂   _·_       renaming (op= to ∙=)
  open FromAssoc _·_ assoc public
  open FromComm  _·_ comm  public

  assoc-comm : ∀ {x y z} → x · (y · z) ≡ y · (x · z)
  assoc-comm = assoc= comm

  !assoc-comm : ∀ {x y z} → (x · y) · z ≡ (x · z) · y
  !assoc-comm = !assoc= comm

  interchange : Interchange _·_ _·_
  interchange = assoc= (!assoc= comm)

  module _ {c d x y x' y' : A}
           (e : (x · y) ≡ (x' · y')) where
    outer= : (x · c) · (d · y) ≡ (x' · c) · (d · y')
    outer= = ∙= comm comm ∙ assoc= (!assoc= e) ∙ ∙= comm comm

module _ {b} {B : Set b} (f : A → B) where
  Injective : Set (b ⊔ a)
  Injective = ∀ {x y} → f x ≡ f y → x ≡ y

  Conflict : Set (b ⊔ a)
  Conflict = ∃ λ x → ∃ λ y → (x ≢ y) × f x ≡ f y

module _ {b} {B : Set b} {f : A → B} where
  Injective-¬Conflict : Injective f → ¬ (Conflict f)
  Injective-¬Conflict inj (x , y , x≢y , fx≡fy) = x≢y (inj fx≡fy)

  Conflict-¬Injective : Conflict f → ¬ (Injective f)
  Conflict-¬Injective = flip Injective-¬Conflict

module Endo {f : A → A} where
  Cycle^ : ℕ → Set _
  Cycle^ n = ∃ λ x → f $⟨ n ⟩ x ≡ x

  Cycle = ∃ Cycle^
-- -}
-- -}
-- -}
-- -}
