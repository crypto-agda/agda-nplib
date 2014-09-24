-- NOTE with-K
module Data.Sum.NP where

open import Data.Sum public renaming (inj₁ to inl; inj₂ to inr)

open import Type hiding (★)
open import Level.NP
open import Function
open import Data.Nat using (ℕ; zero; suc)
open import Data.Zero
open import Data.One
open import Relation.Binary
open import Relation.Binary.Logical
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_;_≢_;_≗_)
open import Data.Two hiding (twist)
open ≡ using (→-to-⟶)

[inl:_,inr:_] = [_,_]

inl-inj : ∀ {a b} {A : ★ a} {B : ★ b} {x y : A} → inl {B = B} x ≡ inl y → x ≡ y
inl-inj ≡.refl = ≡.refl

inr-inj : ∀ {a b} {A : ★ a} {B : ★ b} {x y : B} → inr {A = A} x ≡ inr y → x ≡ y
inr-inj ≡.refl = ≡.refl

module _ {a} {A : ★ a} where
    untag : A ⊎ A → A
    untag = [inl: id ,inr: id ]

module _ {a₁ a₂ b₁ b₂}
         {A₁ : ★ a₁} {A₂ : ★ a₂}
         {B₁ : ★ b₁} {B₂ : ★ b₂}
         {c} {C : ★ c} (f : A₁ ⊎ B₁ → A₂ ⊎ B₂ → C) where
    on-inl = λ i j → f (inl i) (inl j)
    on-inr = λ i j → f (inr i) (inr j)

[,]-assoc : ∀ {a₁ a₂ b₁ b₂ c} {A₁ : ★ a₁} {A₂ : ★ a₂}
              {B₁ : ★ b₁} {B₂ : ★ b₂} {C : ★ c}
              {f₁ : B₁ → C} {g₁ : A₁ → B₁} {f₂ : B₂ → C} {g₂ : A₂ → B₂} →
              [ f₁ , f₂ ] ∘′ map g₁ g₂ ≗ [ f₁ ∘ g₁ , f₂ ∘ g₂ ]
[,]-assoc (inl _) = ≡.refl
[,]-assoc (inr _) = ≡.refl

[,]-factor : ∀ {a₁ a₂ b c} {A₁ : ★ a₁} {A₂ : ★ a₂} {B : ★ b} {C : ★ c}
              {f : B → C} {g₁ : A₁ → B} {g₂ : A₂ → B} →
              [ f ∘ g₁ , f ∘ g₂ ] ≗ f ∘ [ g₁ , g₂ ]
[,]-factor (inl _) = ≡.refl
[,]-factor (inr _) = ≡.refl

map-assoc : ∀ {a₁ a₂ b₁ b₂ c₁ c₂} {A₁ : ★ a₁} {A₂ : ★ a₂}
              {B₁ : ★ b₁} {B₂ : ★ b₂} {C₁ : ★ c₁} {C₂ : ★ c₂}
              {f₁ : B₁ → C₁} {g₁ : A₁ → B₁} {f₂ : B₂ → C₂} {g₂ : A₂ → B₂} →
              map f₁ f₂ ∘′ map g₁ g₂ ≗ map (f₁ ∘ g₁) (f₂ ∘ g₂)
map-assoc = [,]-assoc

open import Data.Product
open import Function.Inverse
open import Function.LeftInverse

{- bad names
⊎-fst : ∀ {a b} {A : ★ a} {B : ★ b} → A ⊎ B → 𝟚
⊎-fst (inl _) = 0₂
⊎-fst (inr _) = 1₂

⊎-snd : ∀ {ℓ} {A B : ★ ℓ} (x : A ⊎ B) → case ⊎-fst x 0: A 1: B
⊎-snd (inl x) = x
⊎-snd (inr x) = x
-}

-- Function.Related.TypeIsomorphisms.NP for the A ⊎ B, Σ 𝟚 [0: A 1: B ] iso.

𝟙⊎^ : ℕ → ★₀
𝟙⊎^ zero    = 𝟘
𝟙⊎^ (suc n) = 𝟙 ⊎ 𝟙⊎^ n

module _ {a b} {A : ★ a} {B : ★ b} where
    twist : A ⊎ B → B ⊎ A
    twist = [inl: inr ,inr: inl ]
