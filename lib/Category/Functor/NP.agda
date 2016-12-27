{-# OPTIONS --without-K #-}
open import Type
open import Relation.Binary
open import Level.NP
open import Function using (id; _∘_; const)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Category.Functor public

module Category.Functor.NP where

Fmap : ∀ {i j ℓ₁ ℓ₂} {I : ★_ i} {J : ★_ j}
         (_↝₁_ : Rel I ℓ₁) (_↝₂_ : Rel J ℓ₂) (F : I → J) → ★_ _
Fmap _↝₁_ _↝₂_ F = ∀ {A B} → A ↝₁ B → F A ↝₂ F B

record IsFunctorial {ℓ} {F : Set ℓ → Set ℓ} (rawFunctor : RawFunctor F) : ★_ (ₛ ℓ) where
  open RawFunctor rawFunctor
  field
    <$>-id : ∀ {A} (x : F A) → (id <$> x) ≡ x

    <$>-∘  : ∀ {A B C} (f : B → C) (g : A → B) x → ((f ∘ g) <$> x) ≡ (f <$> (g <$> x))

  <$-∘ : ∀ {A B C} (f : A → B) (x : C) y → (x <$ y) ≡ (x <$ (f <$> y))
  <$-∘ f x = <$>-∘ (const x) f

record Functor {ℓ} (F : Set ℓ → Set ℓ) : ★_ (ₛ ℓ) where
  field
    rawFunctor   : RawFunctor F
    isFunctorial : IsFunctorial rawFunctor

  open RawFunctor   rawFunctor   public
  open IsFunctorial isFunctorial public
