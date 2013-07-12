{-# OPTIONS --without-K #-}
module Type where

open import Level

★₂ : Set₃
★₂ = Set₂

★₁ : ★₂
★₁ = Set₁

★₀ : ★₁
★₀ = Set

★ : ★₁
★ = ★₀

★_ : ∀ ℓ → Set (suc ℓ)
★_ ℓ = Set ℓ
