{-# OPTIONS --without-K #-}
open import Category.Functor.NP
open import Type
open import Function
open import Level.NP
open import Relation.Binary.PropositionalEquality
open import Data.Vec using (Vec; []; _∷_)

module Category.Monad.NP {ℓ} where

open import Category.Monad public

record IsMonadic {M : Set ℓ → Set ℓ} (rawMonad : RawMonad M) : ★_ (ₛ ℓ) where
  open RawMonad rawMonad

  field
    return->>= : ∀ {A B} (f : A → M B) x → (return x >>= f) ≡ f x
    >>=-return : ∀ {A} (m : M A) → (m >>= return) ≡ m
    >>=-assoc  : ∀ {A B C} (mx : M A) (my : A → M B) (k : B → M C)
                         → (mx >>= λ x → my x >>= k) ≡ (mx >>= my >>= k)

  >>-assoc  : ∀ {A B C} (mx : M A) (my : M B) (mz : M C)
                       → (mx >> (my >> mz)) ≡ ((mx >> my) >> mz)
  >>-assoc mx my mz = >>=-assoc mx (const my) (const mz)

  liftM : ∀ {A B} → (A → B) → M A → M B
  liftM f x = x >>= return ∘ f

  <$>-liftM : ∀ {A B} (f : A → B) x → f <$> x ≡ liftM f x
  <$>-liftM f x = return->>= (λ g → liftM g x) f

  liftM-id : ∀ {A} (mx : M A) → liftM id mx ≡ mx
  liftM-id = >>=-return

  <$>-id : ∀ {A} (mx : M A) → id <$> mx ≡ mx
  <$>-id mx = trans (<$>-liftM id mx) (liftM-id mx)

  {- requires function extensionality
  cong-return-∘ : ∀ {A B : ★_ ℓ} {f g : A → B} → f ≡ g → return ∘ f ≡ return ∘ g
  cong-return-∘ = {!!}

  liftM-∘ : ∀ {A B C} (f : B → C) (g : A → B) x → liftM (f ∘ g) x ≡ liftM f (liftM g x)
  liftM-∘ f g x = trans (cong (_>>=_ x) {!cong-return-∘ {!return->>= (g ?)!}!}) (>>=-assoc x (return ∘ g) (return ∘ f))

  functor : Functor rawFunctor
  functor = record { <$>-id = <$>-id; <$>-∘ = {!!} }
  -}

  vmapM : ∀ {n a}{A : Set a} {B : Set ℓ} → (A → M B) → Vec A n → M (Vec B n)
  vmapM f []       = return []
  vmapM f (x ∷ xs) = _∷_ <$> f x ⊛ vmapM f xs

record Monad (M : Set ℓ → Set ℓ) : ★_ (ₛ ℓ) where
  constructor _,_
  field
    rawMonad  : RawMonad M
    isMonadic : IsMonadic rawMonad

  open RawMonad  rawMonad  public
  open IsMonadic isMonadic public
