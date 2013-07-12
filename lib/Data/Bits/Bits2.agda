{-# OPTIONS --without-K #-}
module Data.Bits.Bits2 where 

open import Data.Bit
open import Data.Bits
open import Data.Nat
open import Data.Vec

bits₂ : Vec (Bits 2) 4
bits₂ = allBits 2

00ᵇ = 0b ∷ 0b ∷ []
01ᵇ = 0b ∷ 1b ∷ []
10ᵇ = 1b ∷ 0b ∷ []
11ᵇ = 1b ∷ 1b ∷ []
