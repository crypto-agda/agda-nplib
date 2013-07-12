{-# OPTIONS --without-K #-}
import Level as L
open import Type
open import Data.Sum using (_⊎_; [_,_])
open import Function.NP
open import Category.Profunctor
open import Category.Applicative

module Lens.Structures {ℓ} where

record Prismatic {i} (_↝_ : ★_ i → ★_ i → ★_ ℓ) : ★_ (ℓ L.⊔ L.suc i) where
  constructor mk
  field
    profunctor : Profunctor _↝_
    prismatic  : ∀ {S T A F} {{F-app : RawApplicative F}}
                 → (S → T ⊎ A)
                 → (A ↝ F T) → (S ↝ F T)
  open Profunctor profunctor public

→Prismatic : Prismatic -→-
→Prismatic = mk →Profunctor (λ st+a aft → [ pure , aft ] ∘ st+a)
  where open RawApplicative {{...}}

record Indexable {i} (_↝_ : ★_ i → ★_ i → ★_ ℓ) : ★_ (ℓ L.⊔ L.suc i) where
  constructor mk
  field
    profunctor : Profunctor _↝_
    indexed    : ∀ {I : ★_ i} {A B} → A ↝ B → I → A → B
  open Profunctor profunctor public

→Indexable : Indexable -→-
→Indexable = mk →Profunctor const
