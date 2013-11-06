-- NOTE with-K
module Data.Sum.NP where

open import Type hiding (★)
open import Level.NP
open import Function
open import Data.Nat using (ℕ; zero; suc)
open import Data.Zero
open import Data.One
open import Data.Sum public
open import Relation.Binary
open import Relation.Binary.Logical
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_;_≢_;_≗_)
open import Data.Two
open ≡ using (→-to-⟶)

inj₁-inj : ∀ {a b} {A : ★ a} {B : ★ b} {x y : A} → _⊎_.inj₁ {B = B} x ≡ inj₁ y → x ≡ y
inj₁-inj ≡.refl = ≡.refl

inj₂-inj : ∀ {a b} {A : ★ a} {B : ★ b} {x y : B} → _⊎_.inj₂ {A = A} x ≡ inj₂ y → x ≡ y
inj₂-inj ≡.refl = ≡.refl

module _ {a₁ a₂ b₁ b₂}
         {A₁ : ★ a₁} {A₂ : ★ a₂}
         {B₁ : ★ b₁} {B₂ : ★ b₂}
         {c} {C : ★ c} (f : A₁ ⊎ B₁ → A₂ ⊎ B₂ → C) where
    on-inj₁ = λ i j → f (inj₁ i) (inj₁ j)
    on-inj₂ = λ i j → f (inj₂ i) (inj₂ j)

[,]-assoc : ∀ {a₁ a₂ b₁ b₂ c} {A₁ : ★ a₁} {A₂ : ★ a₂}
              {B₁ : ★ b₁} {B₂ : ★ b₂} {C : ★ c}
              {f₁ : B₁ → C} {g₁ : A₁ → B₁} {f₂ : B₂ → C} {g₂ : A₂ → B₂} →
              [ f₁ , f₂ ] ∘′ map g₁ g₂ ≗ [ f₁ ∘ g₁ , f₂ ∘ g₂ ]
[,]-assoc (inj₁ _) = ≡.refl
[,]-assoc (inj₂ _) = ≡.refl

[,]-factor : ∀ {a₁ a₂ b c} {A₁ : ★ a₁} {A₂ : ★ a₂} {B : ★ b} {C : ★ c}
              {f : B → C} {g₁ : A₁ → B} {g₂ : A₂ → B} →
              [ f ∘ g₁ , f ∘ g₂ ] ≗ f ∘ [ g₁ , g₂ ]
[,]-factor (inj₁ _) = ≡.refl
[,]-factor (inj₂ _) = ≡.refl

map-assoc : ∀ {a₁ a₂ b₁ b₂ c₁ c₂} {A₁ : ★ a₁} {A₂ : ★ a₂}
              {B₁ : ★ b₁} {B₂ : ★ b₂} {C₁ : ★ c₁} {C₂ : ★ c₂}
              {f₁ : B₁ → C₁} {g₁ : A₁ → B₁} {f₂ : B₂ → C₂} {g₂ : A₂ → B₂} →
              map f₁ f₂ ∘′ map g₁ g₂ ≗ map (f₁ ∘ g₁) (f₂ ∘ g₂)
map-assoc = [,]-assoc

open import Data.Product
open import Function.Inverse
open import Function.LeftInverse

⊎-proj₁ : ∀ {a b} {A : ★ a} {B : ★ b} → A ⊎ B → 𝟚
⊎-proj₁ (inj₁ _) = 0₂
⊎-proj₁ (inj₂ _) = 1₂

⊎-proj₂ : ∀ {ℓ} {A B : ★ ℓ} (x : A ⊎ B) → case ⊎-proj₁ x 0: A 1: B
⊎-proj₂ (inj₁ x) = x
⊎-proj₂ (inj₂ x) = x

-- Function.Related.TypeIsomorphisms.NP for the A ⊎ B, Σ 𝟚 [0: A 1: B ] iso.

𝟙⊎^ : ℕ → ★₀
𝟙⊎^ zero    = 𝟘
𝟙⊎^ (suc n) = 𝟙 ⊎ 𝟙⊎^ n
