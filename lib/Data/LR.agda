{-# OPTIONS --without-K #-}
module Data.LR where

open import Type
open import Function.NP
open import HoTT
open import Relation.Binary.PropositionalEquality.NP using () renaming (refl to idp)
open import Data.Two
open Equivalences

data LR : ★ where
  `L `R : LR

[L:_R:_] : ∀ {ℓ}{C : LR → ★_ ℓ}(l : C `L)(r : C `R)(lr : LR) → C lr
[L: l R: r ] `L = l
[L: l R: r ] `R = r

LR! : LR → LR
LR! `L = `R
LR! `R = `L

LR!-equiv : LR ≃ LR
LR!-equiv = equiv LR! LR! [L: idp R: idp ] [L: idp R: idp ]

isR? : LR → 𝟚
isR? `L = 0₂
isR? `R = 1₂

isL? : LR → 𝟚
isL? = not ∘ isR?

isR?-is-equiv : Is-equiv isR?
isR?-is-equiv = is-equiv [0: `L 1: `R ] [0: idp 1: idp ] [L: idp R: idp ]
