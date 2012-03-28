{-# OPTIONS --universe-polymorphism #-}
module Category.Monad.Partiality.NP where

open import Coinduction
open import Data.Maybe hiding (monad)
open import Data.Nat
open import Level as L
import Category.Monad.Partiality as Pa
import Category.Monad as Cat

module Workaround where
  open Pa.Workaround public

  never : {A : Set} → A ⊥P
  never = later (♯ never)

{- perdicativity/universes limitation…
  monad : ∀ {f} → Cat.RawMonad {f = f} _⊥P
  monad = record
    { return = now
    ; _>>=_  = _>>=_
    }
-}

open Pa public hiding (module Workaround)

module M⊥ ℓ where
  open Cat.RawMonad (Pa.monad {ℓ}) public

open M⊥ L.zero

-- not univ poly yet
_∘⊥_ : ∀ {A B C : Set} → (B → C ⊥) → (A → B ⊥) → (A → C ⊥)
_∘⊥_ f g x = f =<< g x

now? : ∀ {a} {A : Set a} → A ⊥ → Maybe A
now? (now x)   = just x
now? (later _) = nothing

run_for_steps? : ∀ {a} {A : Set a} → A ⊥ → ℕ → Maybe A
run x for n steps? = now? (run x for n steps)
