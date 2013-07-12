{-# OPTIONS --without-K #-}
module Data.Two where

open import Type hiding (★)
open import Data.Product using (_×_; _,_)
import Data.Bool.NP as Bool
open Bool public hiding (if_then_else_; cond) renaming (Bool to 𝟚; false to 0₂; true to 1₂; toℕ to 𝟚▹ℕ; toℕ≤1 to 𝟚≤1)

[0→_,1→_] : ∀ {a} {A : ★ a} → A → A → 𝟚 → A
[0→ e₀ ,1→ e₁ ] b = Bool.if b then e₁ else e₀

case_0→_1→_ : ∀ {a} {A : ★ a} → 𝟚 → A → A → A
case b 0→ e₀ 1→ e₁ = [0→ e₀ ,1→ e₁ ] b

proj : ∀ {a} {A : 𝟚 → ★ a} → A 0₂ × A 1₂ → (b : 𝟚) → A b
proj (x₀ , x₁) 0₂ = x₀
proj (x₀ , x₁) 1₂ = x₁

proj′ : ∀ {a} {A : ★ a} → A × A → 𝟚 → A
proj′ = proj
