{-# OPTIONS --without-K #-}
-- Based on profunctors 4.0.4 haskell package
import Level as L
open import Type hiding (★)
open import Function.NP
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Data.Sum.NP renaming (map to ⊎-map)
open import Data.Product.NP hiding (second) renaming (first to ×-first; second′ to ×-second)

module Category.Profunctor {ℓ} where

record Profunctor {i} (_↝_ : ★ i → ★ i → ★ ℓ) : ★ (ℓ L.⊔ L.suc i) where
  constructor _,_
  field
    lmap : ∀ {A B C} → (A → B) → B ↝ C → A ↝ C
    rmap : ∀ {A B C} → (B → C) → A ↝ B → A ↝ C

  dimap : ∀ {A B C D} → (A → B) → (C → D) → B ↝ C → A ↝ D
  dimap f g = lmap f ∘ rmap g

→-Profunctor : Profunctor {ℓ} -→-
→-Profunctor = flip _∘′_ , _∘′_

------------------------------------------------------------------------------
-- Strong
------------------------------------------------------------------------------

record Strong {i} (_↝_ : ★ i → ★ i → ★ ℓ) : ★ (ℓ L.⊔ L.suc i) where
  constructor mk
  field
    profunctor : Profunctor _↝_
    first      : ∀ {A B C : Set i} → A ↝ B → (A × C) ↝ (B × C)
    second     : ∀ {A B C : Set i} → A ↝ B → (C × A) ↝ (C × B)
  open Profunctor profunctor public

  module _ {A B C : Set i} (second : A ↝ B → (C × A) ↝ (C × B)) where
    first-from-second : A ↝ B → (A × C) ↝ (B × C)
    first-from-second = dimap swap swap ∘ second

  module _ {A B C : Set i} (first : A ↝ B → (A × C) ↝ (B × C)) where
    second-from-first : A ↝ B → (C × A) ↝ (C × B)
    second-from-first = dimap swap swap ∘ first

→-Strong : Strong {ℓ} -→-
→-Strong = mk →-Profunctor ×-first ×-second

------------------------------------------------------------------------------
-- Choice
------------------------------------------------------------------------------

record Choice {i} (_↝_ : ★ i → ★ i → ★ ℓ) : ★ (ℓ L.⊔ L.suc i) where
  constructor mk
  field
    profunctor : Profunctor _↝_
    left       : ∀ {A B C : Set i} → A ↝ B → (A ⊎ C) ↝ (B ⊎ C)
    right      : ∀ {A B C : Set i} → A ↝ B → (C ⊎ A) ↝ (C ⊎ B)
  open Profunctor profunctor public

  module _ {A B C : Set i} (right : A ↝ B → (C ⊎ A) ↝ (C ⊎ B)) where
    left-from-right : A ↝ B → (A ⊎ C) ↝ (B ⊎ C)
    left-from-right = dimap twist twist ∘ right

  module _ {A B C : Set i} (left : A ↝ B → (A ⊎ C) ↝ (B ⊎ C)) where
    right-from-left : A ↝ B → (C ⊎ A) ↝ (C ⊎ B)
    right-from-left = dimap twist twist ∘ left

→-Choice : Choice {ℓ} -→-
→-Choice = mk →-Profunctor (flip ⊎-map id) (⊎-map id)

------------------------------------------------------------------------------
-- UpStar
------------------------------------------------------------------------------

UpStar : (★ ℓ → ★ ℓ) → ★ ℓ → ★ ℓ → ★ ℓ
UpStar F D C = D → F C

module _ {F : ★ ℓ → ★ ℓ} (funF : RawFunctor F) where
    open RawFunctor funF

    upStar-RawFunctor : ∀ {A} → RawFunctor (UpStar F A)
    upStar-RawFunctor = record { _<$>_ = λ k f x → k <$> f x }

    upStar-Profunctor : Profunctor (UpStar F)
    upStar-Profunctor = flip _∘′_
                          , RawFunctor._<$>_ upStar-RawFunctor

    upStar-Strong : Strong (UpStar F)
    upStar-Strong = mk upStar-Profunctor
                       (λ f x → flip _,_ (snd x) <$> f (fst x))
                       (λ f x → _,_ (fst x) <$> f (snd x))

module _ {F : ★ ℓ → ★ ℓ} (appF : RawApplicative F) where
    open RawApplicative appF

    upStar-Choice : Choice (UpStar F)
    upStar-Choice = mk (upStar-Profunctor rawFunctor)
                       (λ f → [inl: _<$>_ inl ∘ f    ,inr: _<$>_ inr ∘ pure ])
                       (λ f → [inl: _<$>_ inl ∘ pure ,inr: _<$>_ inr ∘ f    ])

------------------------------------------------------------------------------
-- DownStar
------------------------------------------------------------------------------

DownStar : (★ ℓ → ★ ℓ) → ★ ℓ → ★ ℓ → ★ ℓ
DownStar F D C = F D → C

downStar-RawFunctor : ∀ {F A} → RawFunctor (DownStar F A)
downStar-RawFunctor = record { _<$>_ = _∘′_ }

downStar-Profunctor : ∀ {F} → RawFunctor F → Profunctor (DownStar F)
downStar-Profunctor fun = (λ f g x → g (f <$> x)) , _∘′_
  where open RawFunctor fun

------------------------------------------------------------------------------
-- Forget
------------------------------------------------------------------------------

Forget : (R A B : Set ℓ) → Set ℓ
Forget R A B = A → R

forget-RawFunctor : ∀ {R A} → RawFunctor (Forget R A)
forget-RawFunctor = record { _<$>_ = const id }

module _ {R} where
    forget-Profunctor : Profunctor (Forget R)
    forget-Profunctor = flip _∘′_ , const id

    forget-Strong : Strong (Forget R)
    forget-Strong = mk forget-Profunctor (λ f → f ∘ fst) (λ f → f ∘ snd)

-- DEPRECATED
record Lenticular {i} (_↝_ : ★ i → ★ i → ★ ℓ) : ★ (ℓ L.⊔ L.suc i) where
  constructor mk
  field
    profunctor : Profunctor _↝_
    lenticular : ∀ {A B} → A ↝ B → A ↝ (A × B)
  open Profunctor profunctor public

→-Lenticular : Lenticular {ℓ} -→-
→-Lenticular = mk →-Profunctor (λ f x → x , f x)

-- -}
-- -}
-- -}
-- -}
