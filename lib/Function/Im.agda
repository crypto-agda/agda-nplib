--TODO {-# OPTIONS --without-K #-}
module Function.Im where

open import Type
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

data Im {A B : ★} (f : A → B) : B → ★ where
  im : ∀ x → Im f (f x)

preIm : ∀ {A B} {f : A → B} {y} → Im f y → A
preIm (im x) = x

leftInverse : ∀ {A B : ★} (f : A → B) (f⁻¹ : (x : B) → Im f x) x → f (preIm (f⁻¹ x)) ≡ x
leftInverse f f⁻¹ x with f⁻¹ x
leftInverse f _ .(f y) | im y = ≡.refl

{-
  rightInverse : ∀ {A B : ★} (f : A → B) (f⁻¹ : (x : B) → Im f x) (x : A) → preIm (f⁻¹ (f x)) ≡ x
  rightInverse f f⁻¹ x with f x     | f⁻¹ (f x)
  rightInverse f f⁻¹ x    | .(f x') | im x' = {!!}
-}

module TestIm where
  open import Data.Nat

  data N2 : ★ where
    zero : N2
    suc : N2 -> N2

  ⇒ : ℕ → N2
  ⇒ zero = zero
  ⇒ (suc n) = suc (⇒ n)

  ⇐ : (x : N2) → Im (⇒) x
  ⇐ zero = im zero
  ⇐ (suc n) with ⇐ n
  ⇐ (suc ._)   | im m = im (suc m)
