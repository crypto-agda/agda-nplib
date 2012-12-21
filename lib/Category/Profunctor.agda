import Level as L
open import Type hiding (★)
open import Function.NP
open import Category.Functor

module Category.Profunctor {ℓ} where

record Profunctor {i} (_↝_ : ★ i → ★ i → ★ ℓ) : ★ (ℓ L.⊔ L.suc i) where
  constructor _,_
  field
    lmap : ∀ {A B C} → (A → B) → B ↝ C → A ↝ C
    rmap : ∀ {A B C} → (B → C) → A ↝ B → A ↝ C

→Profunctor : Profunctor {ℓ} -→-
→Profunctor = flip _∘′_ , _∘′_

UpStar : (★ ℓ → ★ ℓ) → ★ ℓ → ★ ℓ → ★ ℓ
UpStar F D C = D → F C

upStarRawFunctor : ∀ {F A} → RawFunctor F → RawFunctor (UpStar F A)
upStarRawFunctor fun = record { _<$>_ = λ k f x → k <$> f x }
  where open RawFunctor fun

upStarProfunctor : ∀ {F} → RawFunctor F → Profunctor (UpStar F)
upStarProfunctor fun = flip _∘′_
                     , RawFunctor._<$>_ (upStarRawFunctor fun)

DownStar : (★ ℓ → ★ ℓ) → ★ ℓ → ★ ℓ → ★ ℓ
DownStar F D C = F D → C

downStarProfunctor : ∀ {F} → RawFunctor F → Profunctor (DownStar F)
downStarProfunctor fun = (λ f g x → g (f <$> x)) , _∘′_
  where open RawFunctor fun

downStarRawFunctor : ∀ {F A} → RawFunctor (DownStar F A)
downStarRawFunctor = record { _<$>_ = _∘′_ }
