open import Type
open import Function
open import Data.Sum
open import Category.Profunctor
open import Category.Applicative
open import Lens.Structures
open import Lens.Type
open import Lens.Internal
open import Lens.Setter

module Lens.Prism where

Prism : (S T A B : ★) → ★₁
Prism S T A B = ∀ {_↝_ F} {{↝Pri : Prismatic _↝_}} {{Fapp : RawApplicative F}}
                → Overloading _↝_ _↝_ F S T A B

Prism′ : (S A : ★) → ★₁
Prism′ = Simple Prism

APrism : (S T A B : ★) → ★₁
APrism S T A B = Market A B A (Mutator B) → Market A B S (Mutator T)
-- LensLike (Market A B) S T A B

prism : ∀ {S T A B} → (B → T) → (S → T ⊎ A) → Prism S T A B
prism bt st+a = prismatic st+a ∘ rmap (_<$>_ bt)
  where open Prismatic {{...}}
        open RawApplicative {{...}}

{-
Reviewing
remit
review
reviews
reuse
reuses
-}
