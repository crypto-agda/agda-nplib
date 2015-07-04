{-# OPTIONS --without-K #-}
module Data.Product.NP where

open import Type hiding (★)
open import Level
open import Data.Product public hiding (∃) renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Binary.PropositionalEquality.Base as ≡
open import Relation.Unary.NP hiding (Decidable)
open import Relation.Binary.Core
open import Relation.Nullary
open import Function

∃ : ∀ {a b} {A : ★ a} → (A → ★ b) → ★ (a ⊔ b)
∃ = Σ _

first : ∀ {a b c} {A : ★ a} {B : ★ b} {C : B → ★ c} →
          (f : A → B) → Σ A (C ∘ f) → Σ B C
first f = map f id -- f (x , y) = (f x , y)

-- generalized first′ but differently than first
first' : ∀ {a b c} {A : ★ a} {B : A → ★ b} {C : A → ★ c} →
          (f : (x : A) → B x) (p : Σ A C) → B (fst p) × C (fst p)
first' f (x , y) = (f x , y)

first′ : ∀ {a b c} {A : ★ a} {B : ★ b} {C : ★ c} →
          (f : A → B) → A × C → B × C
first′ = first

second : ∀ {a p q} {A : ★ a} {P : A → ★ p} {Q : A → ★ q} →
           (∀ {x} → P x → Q x) → Σ A P → Σ A Q
second = map id

second′ : ∀ {a b c} {A : ★ a} {B : ★ b} {C : ★ c} →
           (B → C) → A × B → A × C
second′ f = second f

syntax ∃ (λ x → e) = ∃[ x ] e

module Dec₂ where
  map₂′ : ∀ {p₁ p₂ q} {P₁ : ★ p₁} {P₂ : ★ p₂} {Q : ★ q}
          → (P₁ → P₂ → Q) → (Q → P₁) → (Q → P₂) → Dec P₁ → Dec P₂ → Dec Q
  map₂′ _   π₁  _   (no ¬p₁)  _         = no (¬p₁ ∘ π₁)
  map₂′ _   _   π₂  _         (no ¬p₂)  = no (¬p₂ ∘ π₂)
  map₂′ mk  _   _   (yes p₁)  (yes p₂)  = yes (mk p₁ p₂)

mkΣ≡ : ∀ {a b} {A : ★ a} {x y : A} (B : A → ★ b) {p : B x} {q : B y} (xy : x ≡ y) → (B ▸ xy) p ≡ q → (x Σ., p) ≡ (y , q)
mkΣ≡ _ xy h rewrite xy | h = ≡.refl

Σ,-injective₁ : ∀ {a b} {A : ★ a} {B : A → ★ b} {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂} → (x₁ , y₁) ≡ (x₂ , y₂) → x₁ ≡ x₂
Σ,-injective₁ = ap fst

fst-injective : ∀ {a b} {A : ★ a} {B : A → ★ b} {x y : Σ A B}
                    (B-uniq : ∀ {z} (p₁ p₂ : B z) → p₁ ≡ p₂)
                  → fst x ≡ fst y → x ≡ y
fst-injective {x = (a , p₁)} {y = (_ , p₂)} B-uniq eq rewrite sym eq
  = ap (λ p → (a , p)) (B-uniq p₁ p₂)

snd-irrelevance : ∀ {a b} {A : ★ a} {B C : A → ★ b} {x₁ x₂ : A}
                      {y₁ : B x₁} {y₂ : B x₂} {z₁ : C x₁} {z₂ : C x₂}
                    → (C-uniq : ∀ {z} (p₁ p₂ : C z) → p₁ ≡ p₂)
                    → (x₁ , y₁) ≡ (x₂ , y₂)
                    → (x₁ , z₁) ≡ (x₂ , z₂)
snd-irrelevance C-uniq = fst-injective C-uniq ∘ Σ,-injective₁

≟Σ' : ∀ {A : ★₀} {P : A → ★₀}
       (decA : Decidable {A = A} _≡_)
       (uniqP : ∀ {x} (p q : P x) → p ≡ q)
     → Decidable {A = Σ A P} _≡_
≟Σ' decA uniqP (w₁ , p₁) (w₂ , p₂) with decA w₁ w₂
≟Σ' decA uniqP (w  , p₁) (.w , p₂) | yes refl
  = yes (ap (λ p → (w , p)) (uniqP p₁ p₂))
≟Σ' decA uniqP (w₁ , p₁) (w₂ , p₂) | no w≢ = no (w≢ ∘ ap fst)

Δ : ∀ {a} {A : ★ a} → A → A × A
Δ x = x , x

ΣΣ : ∀ {a b c} (A : ★ a) (B : A → ★ b) (C : Σ A B → ★ c) → ★ _
ΣΣ A B C = Σ A λ x → Σ (B x) λ y → C (x , y)

ΣΣΣ : ∀ {a b c d} (A : ★ a) (B : A → ★ b)
                  (C : Σ A B → ★ c) (D : Σ (Σ A B) C → ★ d) → ★ _
ΣΣΣ A B C D = Σ A λ x → Σ (B x) λ y → Σ (C (x , y)) λ z → D ((x , y) , z)
