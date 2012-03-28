{-# OPTIONS --universe-polymorphism #-}
module Data.List.NP where

open import Data.List  public
open import Data.Bool  using (Bool; not; if_then_else_)
open import Data.Nat   using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Function   using (_∘_)

-- Move this
Eq : ∀ {a} → Set a → Set a
Eq A = (x₁ x₂ : A) → Bool

uniqBy : ∀ {A : Set} → Eq A → List A → List A
uniqBy _==_ []       = []
uniqBy _==_ (x ∷ xs) = x ∷ filter (not ∘ _==_ x) (uniqBy _==_ xs)
                    -- x ∷ uniqBy _==_ (filter (not ∘ _==_ x) xs)

listToMaybe : ∀ {a} {A : Set a} → List A → Maybe A
listToMaybe []      = nothing
listToMaybe (x ∷ _) = just x

findIndices : ∀ {a} {A : Set a} → (A → Bool) → List A → List ℕ
-- findIndices p xs = [ i | (x,i) <- zip xs [0..], p x ]
findIndices {A = A} p = go 0 where
  go : ℕ → List A → List ℕ
  go _ []       = []
  go i (x ∷ xs) = if p x then i ∷ go (suc i) xs else go (suc i) xs

findIndex : ∀ {a} {A : Set a} → (A → Bool) → List A → Maybe ℕ
findIndex p = listToMaybe ∘ findIndices p

index : ∀ {a} {A : Set a} → Eq A → A → List A → Maybe ℕ
index _==_ x = findIndex (_==_ x)
