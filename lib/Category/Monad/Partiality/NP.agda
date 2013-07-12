{-# OPTIONS --without-K #-}
module Category.Monad.Partiality.NP where

open import Type hiding (★)
open import Coinduction
open import Data.Maybe hiding (monad)
open import Data.Nat
open import Level as L
import Category.Monad.Partiality as Pa
import Category.Monad as Cat

module Workaround {a} where
  open Pa.Workaround {a} public

  never : ∀ {A} → A ⊥P
  never = later (♯ never)

{- because universe levels _⊥P is not an endofunctor,
   therefore _⊥P is not a proper monad.

  monad : ∀ {f} → Cat.RawMonad {f = f} _⊥P
  monad = record
    { return = now
    ; _>>=_  = _>>=_
    }
-}

open Pa public hiding (module Workaround)

module M⊥ ℓ where
  open Cat.RawMonad (Pa.monad {ℓ}) public

_∘⊥_ : ∀ {ℓ a} {A : ★ a} {B C : ★ ℓ} → (B → C ⊥) → (A → B ⊥) → (A → C ⊥)
(f ∘⊥ g) x = f =<< g x where open M⊥ _

now? : ∀ {a} {A : ★ a} → A ⊥ → Maybe A
now? (now x)   = just x
now? (later _) = nothing

run_for_steps? : ∀ {a} {A : ★ a} → A ⊥ → ℕ → Maybe A
run x for n steps? = now? (run x for n steps)
