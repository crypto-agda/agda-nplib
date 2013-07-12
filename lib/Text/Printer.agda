{-# OPTIONS --without-K #-}
module Text.Printer where

open import Type
open import Data.String
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable

ShowS : ★
ShowS = String → String

Pr : ★ → ★
Pr A = A → ShowS

`_ : String → ShowS
(` s) tail = Data.String._++_ s tail

parenBase : ShowS → ShowS
parenBase doc = ` "(" ∘ doc ∘ ` ")"

record PrEnv : ★ where
  constructor mk
  field
    level : ℕ

  withLevel : ℕ → PrEnv
  withLevel x = record { level = x }

open PrEnv

paren : PrEnv → PrEnv → ShowS → ShowS
paren Γ Δ = if ⌊ level Γ ≤? level Δ ⌋ then id else parenBase
