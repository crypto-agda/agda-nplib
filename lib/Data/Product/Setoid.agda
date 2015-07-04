{-# OPTIONS --without-K #-}
module Data.Product.Setoid where

open import Data.Product.NP
open import Relation.Binary.PropositionalEquality
open import Function.Injection using (Injection; module Injection)

fst-Injection : ∀ {a b} {A : Set a} {B : A →  Set b}
                  → (∀ {x} (p₁ p₂ : B x) → p₁ ≡ p₂)
                  → Injection (setoid (Σ A B))
                              (setoid A)
fst-Injection {B = B} B-uniq
     = record { to        = →-to-⟶ (fst {B = B})
              ; injective = fst-injective B-uniq
              }
