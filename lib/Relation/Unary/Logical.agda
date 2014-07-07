{-# OPTIONS --without-K #-}
module Relation.Unary.Logical where

open import Type hiding (★)
open import Level
open import Algebra.FunctionProperties
open import Relation.Unary.NP hiding (Decidable)
open import Relation.Binary

[★] : ∀ {a} aₚ (A : ★ a) → ★ _
[★] aₚ A = A → ★ aₚ

[★₀] : ∀ (A : ★₀) → ★₁
[★₀] = [★] zero

[★₁] : ∀ (A : ★₁) → ★₂
[★₁] = [★] (suc zero)

[Set₀] : Set₀ → Set₁
[Set₀] = λ A → A → Set₀

[Set₁] : Set₁ → Set₂
[Set₁] = λ A → A → Set₁

[Π] : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
        {b bₚ} {B : A → ★ b} (Bₚ : ∀ {x} (xₚ : Aₚ x) → B x → ★ bₚ)
        (f : (x : A) → B x) → ★ _
[Π] Aₚ Bₚ = λ f → ∀ {x} (xₚ : Aₚ x) → Bₚ xₚ (f x)

infixr 0 [Π]
syntax [Π] Aₚ (λ xₚ → f) = ⟨ xₚ ∶ Aₚ ⟩[→] f

[Π]e : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
         {b bₚ} {B : A → ★ b} (Bₚ : ∀ {x} (xₚ : Aₚ x) → B x → ★ bₚ)
         (f : (x : A) → B x) → ★ _
[Π]e Aₚ Bₚ = λ f → ∀ x (xₚ : Aₚ x) → Bₚ xₚ (f x)

[∀] : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
        {b bₚ} {B : A → ★ b} (Bₚ : ∀ {x} (xₚ : Aₚ x) → B x → ★ bₚ)
        (f : {x : A} → B x) → ★ _
[∀] Aₚ Bₚ = λ f → ∀ {x} (xₚ : Aₚ x) → Bₚ xₚ (f {x})

-- more implicit than [∀]
[∀]i : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
         {b bₚ} {B : A → ★ b} (Bₚ : ∀ {x} (xₚ : Aₚ x) → B x → ★ bₚ)
         (f : {x : A} → B x) → ★ _
[∀]i Aₚ Bₚ = λ f → ∀ {x} {xₚ : Aₚ x} → Bₚ xₚ (f {x})

infixr 0 [∀] [∀]i
syntax [∀]  Aₚ (λ xₚ → f) = ∀⟨ xₚ ∶ Aₚ ⟩[→] f
syntax [∀]i Aₚ (λ xₚ → f) = ∀i⟨ xₚ ∶ Aₚ ⟩[→] f

infixr 1 _[→]_
_[→]_ : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
          {b bₚ} {B : ★ b} (Bₚ : B → ★ bₚ)
          (f : A → B) → ★ _
Aₚ [→] Bₚ = [Π] Aₚ (λ _ → Bₚ)

infixr 0 _[→]e_
_[→]e_ : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
           {b bₚ} {B : ★ b} (Bₚ : B → ★ bₚ)
           (f : A → B) → ★ _
_[→]e_ Aₚ Bₚ = [Π]e Aₚ (λ _ → Bₚ)

open import Data.Product
open import Data.One

record [𝟙] (x : 𝟙) : ★₀ where
  constructor [0₁]

open import Data.Zero

data [𝟘] (x : 𝟘) : ★₀ where

open import Relation.Nullary

infix 3 [¬]_

[¬]_ : ∀ {a aₚ} → ([★] {a} aₚ [→] [★] _) ¬_
[¬] Aₚ = Aₚ [→] [𝟘]

-- Products [Σ], [∃], [×] are in Data.Product.NP

[Pred] : ∀ {p} pₚ {a aₚ} → ([★] {a} aₚ [→] [★] _) (Pred p)
[Pred] pₚ Aₚ = Aₚ [→] [★] pₚ

private
  REL′ : ∀ r {a b} → ★ a → ★ b → ★ (a ⊔ b ⊔ suc r)
  REL′ r A B = A → B → ★ r

  [REL]′ : ∀ {r} rₚ {a aₚ b bₚ} →
          ([★] {a} aₚ [→] [★] {b} bₚ [→] [★] _) (REL′ r)
  [REL]′ rₚ Aₚ Bₚ = Aₚ [→] Bₚ [→] ([★] rₚ)

[REL] : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
          {b bₚ} {B : ★ b} (Bₚ : B → ★ bₚ)
          {r} rₚ (∼ : REL A B r) → ★ _
[REL] Aₚ Bₚ rₚ = Aₚ [→] Bₚ [→] ([★] rₚ)

[Rel] : ∀ {a aₚ} {A : ★ a} (Aₚ : A → ★ aₚ)
          {r} rₚ (∼ : Rel A r) → ★ _
[Rel] Aₚ rₚ = [REL] Aₚ Aₚ rₚ

data [Dec] {p pₚ} {P : ★ p} (Pₚ : P → ★ pₚ) : [★] (p ⊔ pₚ) (Dec P) where
  yes : ∀ {p : P}    (pₚ : Pₚ p) → [Dec] Pₚ (yes p)
  no  : ∀ {¬p : ¬ P} (¬pₚ : ([¬] Pₚ) ¬p) → [Dec] Pₚ (no ¬p)

private
  [Dec]' : ∀ {p} → [Pred] {p} p ([★] p) Dec
  [Dec]' = [Dec]

[Decidable] : ∀ {a aₚ b bₚ r rₚ}
              → (∀⟨ Aₚ ∶ [★] {a} aₚ ⟩[→]
                 ∀⟨ Bₚ ∶ [★] {b} bₚ ⟩[→]
                   [REL] Aₚ Bₚ {r} rₚ [→] [★] _) Decidable
[Decidable] Aₚ Bₚ _∼ₚ_ = ⟨ xₚ ∶ Aₚ ⟩[→] ⟨ yₚ ∶ Bₚ ⟩[→] [Dec] (xₚ ∼ₚ yₚ)

[Op₁] : ∀ {a} → ([★] {a} a [→] [★] a) Op₁
[Op₁] Aₚ = Aₚ [→] Aₚ

[Op₂] : ∀ {a aₚ} → ([★] {a} (a ⊔ aₚ) [→] [★] (a ⊔ aₚ)) Op₂
[Op₂] Aₚ = Aₚ [→] Aₚ [→] Aₚ
