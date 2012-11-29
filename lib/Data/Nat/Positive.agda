module Data.Nat.Positive where

open import Type
open import Data.Nat renaming (_*_ to _*ℕ_; _+_ to _+ℕ_)

data ℕ⁺ : ★ where
  suc : ℕ → ℕ⁺

one : ℕ⁺
one = suc zero

_+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
suc x + suc y = suc (suc (x +ℕ y))

_*_ : ℕ⁺ → ℕ⁺ → ℕ⁺
suc x * suc y = suc (x +ℕ y +ℕ x *ℕ y)
