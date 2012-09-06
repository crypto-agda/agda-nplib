module Text.Printer where

open import Data.String
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable

ShowS : Set
ShowS = String → String

Pr : Set → Set
Pr A = A → ShowS

`_ : String → ShowS
(` s) tail = Data.String._++_ s tail

parenBase : ShowS → ShowS
parenBase doc = ` "(" ∘ doc ∘ ` ")"

record PrEnv : Set where
  constructor mk
  field
    level : ℕ

  withLevel : ℕ → PrEnv
  withLevel x = record { level = x }

open PrEnv

paren : (PrEnv → PrEnv) → PrEnv → ShowS → ShowS
paren f Δ = if ⌊ level (f Δ) ≤? level Δ ⌋ then id else parenBase
