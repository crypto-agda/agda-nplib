{-# OPTIONS --without-K #-}
module Data.List.NP where

open import Type hiding (★)
open import Category.Monad
open import Category.Applicative.NP
open import Data.List  public
open import Data.Two   using (𝟚; not; case_0:_1:_)
open import Data.Nat   using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Function   using (_∘_)

module Monad {ℓ} where
  open RawMonad (monad {ℓ}) public
  open RawApplicative rawIApplicative public using (replicateM)

-- Move this
Eq : ∀ {a} → ★ a → ★ a
Eq A = (x₁ x₂ : A) → 𝟚

module _ {a} {A : ★ a} where
    uniqBy : Eq A → List A → List A
    uniqBy _==_ []       = []
    uniqBy _==_ (x ∷ xs) = x ∷ filter (not ∘ _==_ x) (uniqBy _==_ xs)
                        -- x ∷ uniqBy _==_ (filter (not ∘ _==_ x) xs)

    listToMaybe : List A → Maybe A
    listToMaybe []      = nothing
    listToMaybe (x ∷ _) = just x

    findIndices : (A → 𝟚) → List A → List ℕ
    -- findIndices p xs = [ i | (x,i) <- zip xs [0..], p x ]
    findIndices p = go 0 where
      go : ℕ → List A → List ℕ
      go _ []       = []
      go i (x ∷ xs) = case p x 0: go (suc i) xs
                               1: (i ∷ go (suc i) xs)

module _ {a} {A : ★ a} where
    findIndex : (A → 𝟚) → List A → Maybe ℕ
    findIndex p = listToMaybe ∘ findIndices p

    index : Eq A → A → List A → Maybe ℕ
    index _==_ x = findIndex (_==_ x)

    find : (p : A → 𝟚) → List A → Maybe A
    find p = listToMaybe ∘ filter p

    dup : List A → List A
    dup x = x ++ x
