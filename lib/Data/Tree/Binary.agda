{-# OPTIONS --without-K #-}
open import Type hiding (★)

open import Level
open import Data.Zero
open import Data.Sum

module Data.Tree.Binary where

data BinTree {a} (A : ★ a) : ★ a where
  empty : BinTree A
  leaf  : A → BinTree A
  fork  : (ℓ r : BinTree A) → BinTree A

Any : ∀ {a p}{A : ★ a}(P : A → ★ p) → BinTree A → ★ p
Any P empty = Lift 𝟘
Any P (leaf x) = P x
Any P (fork ts ts₁) = Any P ts ⊎ Any P ts₁
