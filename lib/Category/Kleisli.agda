{-# OPTIONS --without-K #-}
module Category.Kleisli where

open import Type hiding (★)
open import Relation.Binary using (Rel)
open import Category
open import Category.Monad

Kleisli : ∀ {ℓ} (M : ★ ℓ → ★ ℓ) → Rel (★ ℓ) ℓ
Kleisli M A B = A → M B

kleisli-RawCategory : ∀ {ℓ M} → RawMonad M → RawCategory (Kleisli {ℓ} M)
kleisli-RawCategory mon = record { id  = return
                                 ; _∘_ = λ f g x → g x >>= f }
  where open RawMonad mon
