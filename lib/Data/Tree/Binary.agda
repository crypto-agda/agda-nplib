{-# OPTIONS --without-K #-}
open import Type hiding (★)

open import Level
open import Function
open import Data.Zero
open import Data.One
open import Data.Sum     hiding (map)
open import Data.Product hiding (map)
open import Data.Bits    hiding (map; replicate)
open import Data.Nat
import Data.Tree.Binary.Perfect as P

module Data.Tree.Binary where

data BinTree {a} (A : ★ a) : ★ a where
  empty : BinTree A
  leaf  : A → BinTree A
  fork  : (ℓ r : BinTree A) → BinTree A

private
    T = BinTree

Any : ∀ {a p}{A : ★ a}(P : A → ★ p) → T A → ★ p
Any P empty = Lift 𝟘
Any P (leaf x) = P x
Any P (fork t u) = Any P t ⊎ Any P u

All : ∀ {a p}{A : ★ a}(P : A → ★ p) → T A → ★ p
All P empty = Lift 𝟙
All P (leaf x) = P x
All P (fork t u) = All P t × All P u

_=<<_ : ∀ {a b} {A : Set a} {B : Set b}
        → (A → T B) → T A → T B
f =<< empty    = empty
f =<< leaf x   = f x
f =<< fork t u = fork (f =<< t) (f =<< u)

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → T A → T B
map f t = (leaf ∘ f) =<< t

module _ {a} {A : Set a} where
    from-Perfect : ∀ {n} → P.Tree A n → T A
    from-Perfect (P.leaf x)   = leaf x
    from-Perfect (P.fork t t₁) = fork (from-Perfect t) (from-Perfect t₁)

    replicate : ℕ → A → T A
    replicate n x = from-Perfect (P.replicate n x)

    from-fun : ∀ {n} → (Bits n → A) → T A
    from-fun = from-Perfect ∘ P.from-fun
