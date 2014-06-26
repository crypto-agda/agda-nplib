{-# OPTIONS --without-K #-}
module Level.NP where

import Level
open import Data.Nat

open Level public renaming (zero to ₀; suc to ₛ)

₁ ₂ ₃ ₄ : Level
₁ = ₛ ₀
₂ = ₛ ₁
₃ = ₛ ₂
₄ = ₛ ₃

ℕ→Level : ℕ → Level
ℕ→Level zero    = ₀
ℕ→Level (suc n) = ₛ (ℕ→Level n)
