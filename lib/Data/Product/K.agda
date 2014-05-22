open import Function
open import Type hiding (★)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary

module Data.Product.K where

Σ,-injective₂ : ∀ {a b} {A : ★ a} {B : A → ★ b} {x : A} {y z : B x} → (_,_ {B = B} x y) ≡ (x , z) → y ≡ z
Σ,-injective₂ refl = refl
-- Σ,-injective₂ {A = A} {B} {x} {y} {z} p = {!apd snd p!}

≟Σ : ∀ {A : ★₀} {P : A → ★₀}
       (decA : Decidable {A = A} _≡_)
       (decP : ∀ x → Decidable {A = P x} _≡_)
     → Decidable {A = Σ A P} _≡_
≟Σ decA decP (w₁ , p₁) (w₂ , p₂) with decA w₁ w₂
≟Σ decA decP (w  , p₁) (.w , p₂) | yes refl with decP w p₁ p₂
≟Σ decA decP (w  , p)  (.w , .p) | yes refl | yes refl = yes refl
≟Σ decA decP (w  , p₁) (.w , p₂) | yes refl | no  p≢
    = no (p≢ ∘ Σ,-injective₂)
≟Σ decA decP (w₁ , p₁) (w₂ , p₂) | no w≢ = no (w≢ ∘ cong fst)
