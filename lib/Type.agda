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

Type₂ : Set₃
Type₂ = Set₂

Type₁ : Type₂
Type₁ = Set₁

Type₀ : Type₁
Type₀ = Set

Type : Type₁
Type = Type₀

Type_ : ∀ ℓ → Set (suc ℓ)
Type_ ℓ = Set ℓ
