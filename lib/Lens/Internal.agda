open import Type
open import Function
open import Data.Sum
open import Category.Applicative
open import Category.Profunctor
open import Lens.Structures

module Lens.Internal where

Market : (A B S T : ★) → ★₁
Market A B S T = ∀ {R} → ((B → T) → (S → T ⊎ A) → R) → R

module Markets {A B} where
  _↝_ : ★ → ★ → ★₁
  S ↝ T = Market A B S T

  -- rmap/fmap
  rmap : ∀ {S T T'} → (T → T') → S ↝ T → S ↝ T'
  rmap f x = x λ bt st+a k → k (f ∘ bt) ([ inj₁ ∘ f , inj₂ ] ∘ st+a)

  lmap : ∀ {S S' T} → (S' → S) → S ↝ T → S' ↝ T
  lmap f x = x λ bt st+a k → k bt (st+a ∘ f)

  prismatic : ∀ {S T A F} {{F-app : RawApplicative F}}
              → (S → T ⊎ A)
              → (A ↝ F T) → (S ↝ F T)
  prismatic f x = x λ bt aft+a k → k bt ([ inj₁ ∘ pure , aft+a ] ∘ f)
    where open RawApplicative {{...}}

marketPrismatic : ∀ {A B} → Prismatic (Market A B)
marketPrismatic = mk (lmap , rmap) prismatic
  where open Markets
