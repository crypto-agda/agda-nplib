{-# OPTIONS --without-K #-}
module Level.NP where

import Level

open Level public renaming (zero to ₀; suc to ₛ)

₁ ₂ ₃ ₄ : Level
₁ = ₛ ₀
₂ = ₛ ₁
₃ = ₛ ₂
₄ = ₛ ₃
