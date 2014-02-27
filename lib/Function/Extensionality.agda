{-# OPTIONS --without-K #-}
module Function.Extensionality where

open import Relation.Binary.PropositionalEquality

postulate
    FunExt : Set
    λ= : ∀ {a b}{A : Set a}{B : A → Set b}{f₀ f₁ : (x : A) → B x}(f= : ∀ x → f₀ x ≡ f₁ x){{fe : FunExt}} → f₀ ≡ f₁
