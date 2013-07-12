{-# OPTIONS --without-K #-}
module Data.List.NP where

open import Type hiding (★)
open import Category.Monad
open import Category.Applicative.NP
open import Data.List  public
open import Data.Bool  using (Bool; not; if_then_else_)
open import Data.Nat   using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Function   using (_∘_)

module Monad {ℓ} where
  open RawMonad (monad {ℓ}) public
  open RawApplicative rawIApplicative public using (replicateM)

-- Move this
Eq : ∀ {a} → ★ a → ★ a
Eq A = (x₁ x₂ : A) → Bool

uniqBy : ∀ {a} {A : ★ a} → Eq A → List A → List A
uniqBy _==_ []       = []
uniqBy _==_ (x ∷ xs) = x ∷ filter (not ∘ _==_ x) (uniqBy _==_ xs)
                    -- x ∷ uniqBy _==_ (filter (not ∘ _==_ x) xs)

listToMaybe : ∀ {a} {A : ★ a} → List A → Maybe A
listToMaybe []      = nothing
listToMaybe (x ∷ _) = just x

findIndices : ∀ {a} {A : ★ a} → (A → Bool) → List A → List ℕ
-- findIndices p xs = [ i | (x,i) <- zip xs [0..], p x ]
findIndices {A = A} p = go 0 where
  go : ℕ → List A → List ℕ
  go _ []       = []
  go i (x ∷ xs) = if p x then i ∷ go (suc i) xs else go (suc i) xs

findIndex : ∀ {a} {A : ★ a} → (A → Bool) → List A → Maybe ℕ
findIndex p = listToMaybe ∘ findIndices p

index : ∀ {a} {A : ★ a} → Eq A → A → List A → Maybe ℕ
index _==_ x = findIndex (_==_ x)
