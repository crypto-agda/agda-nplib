{-# OPTIONS --without-K #-}
module Data.Bit where

import Data.Two
open Data.Two public renaming (𝟚 to Bit; 0₂ to 0b; 1₂ to 1b; 𝟚▹ℕ to Bit▹ℕ)
