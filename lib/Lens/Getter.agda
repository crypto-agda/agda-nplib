{-# OPTIONS --without-K #-}
-- Inspired from the haskell 'lens' package
module Lens.Getter where

open import Type
open import Lens.Type
open import Function

data Accessor (R : ★) (A : ★) : ★ where
  mkAccessor : R → Accessor R A

private
  coerceAccessor : ∀ {R A B} → Accessor R A → Accessor R B
  coerceAccessor (mkAccessor x) = mkAccessor x
  runAccessor : ∀ {R A} → Accessor R A → R
  runAccessor (mkAccessor x) = x

Getting : (R S T A B : ★) → ★
Getting R = LensLike (Accessor R)
  -- Getting R S T A B ≡ (A → Accessor R B) → S → Accessor R T

-- unlike Control.Lens.Getter we have no Gettable type-class
Getter : (S A : ★) → ★₁
Getter S A = ∀ {R} → Getting R S S A A

infixl 8 _^·_ _^&_
infixl 1 _&_
infixr 0 _^$_
 
_^·_ : ∀ {S T A B} → S → Getting A S T A B → A
s ^· ℓ = runAccessor (ℓ mkAccessor s)
 
_^$_ : ∀ {S T A B} → Getting A S T A B → S → A
_^$_ = flip _^·_

to : ∀ {S A} → (S → A) → Getter S A
to f g = coerceAccessor ∘ g ∘ f

_&_ : ∀ {A B : ★} → A → (A → B) → B
a & f = f a

_^&_ : ∀ {A B : ★} → A → (A → B) → B
a ^& f = f a
