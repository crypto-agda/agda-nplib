{-# OPTIONS --without-K #-}
-- Inspired from the haskell 'lens' package
module Lens.Setter where

open import Type
open import Function.NP
open import Lens.Type
open import Category.Applicative
open import Category.Functor

data Mutator (A : ★) : ★ where
  mkMutator : A → Mutator A

private
  runMutator : ∀ {A} → Mutator A → A
  runMutator (mkMutator x) = x

Setting : (S T A B : ★) → ★
Setting = LensLike Mutator
  -- Setting S T A B = (A → Mutator B) → S → Mutator T

SimpleSetting : (S A : ★) → ★
SimpleSetting = Simple Setting

-- | Anything 'Settable' must be isomorphic to the 'Identity' 'Functor'.
record Settable (F : ★ → ★) : ★₁ where
  constructor mk
  field
    isApplicative : RawApplicative F
    untainted : ∀ {A} → F A → A
  open RawApplicative isApplicative public
-- more instances: Backward, Compose

idSettable : Settable id
idSettable = mk id-app id

MutatorRawFunctor : RawFunctor Mutator
MutatorRawFunctor = record { _<$>_ = λ f → mkMutator ∘ f ∘ runMutator }

MutatorRawApplicative : RawApplicative Mutator
MutatorRawApplicative = record { pure = mkMutator; _⊛_ = λ f x → mkMutator (runMutator f (runMutator x)) }

MutatorSettable : Settable Mutator
MutatorSettable = mk MutatorRawApplicative runMutator

Setter : (S T A B : ★) → ★₁
Setter S T A B = ∀ {F : ★ → ★} {{sF : Settable F}} → LensLike F S T A B  

SimpleSetter : (S A : ★) → ★₁
SimpleSetter = Simple Setter

sets : ∀ {A B S T} → ((A → B) → S → T) → Setter S T A B
sets f g = pure ∘ f (untainted ∘ g)
  where open Settable {{...}}

mapped : ∀ {F A B} {{_ : RawFunctor F}} → Setter (F A) (F B) A B
mapped = sets _<$>_
  where open RawFunctor {{...}}
