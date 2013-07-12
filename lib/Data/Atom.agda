{-# OPTIONS --without-K #-}
module Data.Atom where

open import Type
open import Data.Nat.NP as Nat
open import Data.Bool
open import Data.List
open import Function
open import Relation.Binary.PropositionalEquality

module Internals where
  Atom : ★
  Atom = ℕ

  _==ᴬ_ : (x y : Atom) → Bool
  _==ᴬ_ = Nat._==_

  _ᴬ : ℕ → Atom
  _ᴬ = id

  rmᴬ : Atom → List Atom → List Atom
  rmᴬ a []         = []
  rmᴬ a (x ∷ xs)   = if a ==ᴬ x then rmᴬ a xs else x ∷ rmᴬ a xs

  injᴬ : ∀ {m n} → m ᴬ ≡ n ᴬ → m ≡ n
  injᴬ = id

abstract
  Atom : ★
  Atom = Internals.Atom

  _==ᴬ_ : (x y : Atom) → Bool
  _==ᴬ_ = Internals._==ᴬ_

  _ᴬ : ℕ → Atom
  _ᴬ = Internals._ᴬ

  rmᴬ : Atom → List Atom → List Atom
  rmᴬ = Internals.rmᴬ

  injᴬ : ∀ {m n} → m ᴬ ≡ n ᴬ → m ≡ n
  injᴬ = Internals.injᴬ
