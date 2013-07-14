{-# OPTIONS --without-K #-}
module Data.Product.NP where

open import Type hiding (★)
open import Level
open import Data.Product public hiding (∃)
open import Relation.Binary.PropositionalEquality.NP as ≡
open import Relation.Unary.NP hiding (Decidable)
open import Relation.Binary
open import Relation.Nullary
open import Function
open import Function.Injection using (Injection; module Injection)
open import Relation.Unary.Logical
open import Relation.Binary.Logical

∃ : ∀ {a b} {A : ★ a} → (A → ★ b) → ★ (a ⊔ b)
∃ = Σ _

first : ∀ {a b c} {A : ★ a} {B : ★ b} {C : B → ★ c} →
          (f : A → B) → Σ A (C ∘ f) → Σ B C
first f = map f id -- f (x , y) = (f x , y)

-- generalized first′ but differently than first
first' : ∀ {a b c} {A : ★ a} {B : A → ★ b} {C : A → ★ c} →
          (f : (x : A) → B x) (p : Σ A C) → B (proj₁ p) × C (proj₁ p)
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

record [Σ] {a b aₚ bₚ}
           {A : ★ a}
           {B : A → ★ b}
           (Aₚ : A → ★ aₚ)
           (Bₚ : {x : A} (xₚ : Aₚ x)
                 → B x → ★ bₚ)
           (p : Σ A B) : ★ (aₚ ⊔ bₚ) where
  constructor _[,]_
  field
    [proj₁] : Aₚ (proj₁ p)
    [proj₂] : Bₚ [proj₁] (proj₂ p)
open [Σ] public
infixr 4 _[,]_

syntax [Σ] Aₚ (λ xₚ → e) = [ xₚ ∶ Aₚ ][×][ e ]

[∃] : ∀ {a aₚ b bₚ} →
        (∀i⟨ Aₚ ∶ [★] {a} aₚ ⟩[→] ((Aₚ [→] [★] {b} bₚ) [→] [★] _)) ∃
[∃] {xₚ = Aₚ} = [Σ] Aₚ

syntax [∃] (λ Aₚ → f) = [∃][ Aₚ ] f

_[×]_ : ∀ {a b aₚ bₚ} → ([★] {a} aₚ [→] [★] {b} bₚ [→] [★] _) _×_
_[×]_ Aₚ Bₚ = [Σ] Aₚ (λ _ → Bₚ)

private

  Dec⟦★⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂}
               (Aᵣ : ⟦★⟧ aᵣ A₁ A₂)
             → ★ _
  Dec⟦★⟧ Aᵣ = ∀ x₁ x₂ → Dec (Aᵣ x₁ x₂)

  Dec⟦Pred⟧ : ∀ {a₁ a₂ p₁ p₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂}
                (Aᵣ : ⟦★⟧ aᵣ A₁ A₂)
                {P₁ : Pred p₁ A₁} {P₂ : Pred p₂ A₂} {pᵣ}
              → (Pᵣ : ⟦Pred⟧ pᵣ Aᵣ P₁ P₂) → ★ _
  Dec⟦Pred⟧ {A₁ = A₁} {A₂} Aᵣ {P₁} {P₂} Pᵣ = ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) y₁ y₂ → Dec (Pᵣ xᵣ y₁ y₂) -- Dec⟦★⟧ Aᵣ ⇒ Dec⟦★⟧ Pᵣ

record ⟦Σ⟧ {a₁ a₂ b₂ b₁ aᵣ bᵣ}
           {A₁ : ★ a₁} {A₂ : ★ a₂}
           {B₁ : A₁ → ★ b₁}
           {B₂ : A₂ → ★ b₂}
           (Aᵣ : A₁ → A₂ → ★ aᵣ)
           (Bᵣ : {x₁ : A₁} {x₂ : A₂} (xᵣ : Aᵣ x₁ x₂)
                → B₁ x₁ → B₂ x₂ → ★ bᵣ)
           (p₁ : Σ A₁ B₁) (p₂ : Σ A₂ B₂) : ★ (aᵣ ⊔ bᵣ) where
  constructor _⟦,⟧_
  field
    ⟦proj₁⟧ : Aᵣ (proj₁ p₁) (proj₁ p₂)
    ⟦proj₂⟧ : Bᵣ ⟦proj₁⟧ (proj₂ p₁) (proj₂ p₂)
open ⟦Σ⟧ public
infixr 4 _⟦,⟧_

syntax ⟦Σ⟧ Aᵣ (λ xᵣ → e) = [ xᵣ ∶ Aᵣ ]⟦×⟧[ e ]

⟦∃⟧ : ∀ {a₁ a₂ b₂ b₁ aᵣ bᵣ}
        {A₁ : ★ a₁} {A₂ : ★ a₂}
        {Aᵣ : A₁ → A₂ → ★ aᵣ}
        {B₁ : A₁ → ★ b₁}
        {B₂ : A₂ → ★ b₂}
        (Bᵣ : ⟦Pred⟧ bᵣ Aᵣ B₁ B₂)
        (p₁ : Σ A₁ B₁) (p₂ : Σ A₂ B₂) → ★ _
⟦∃⟧ = ⟦Σ⟧ _

syntax ⟦∃⟧ (λ xᵣ → e) = ⟦∃⟧[ xᵣ ] e

_⟦×⟧_ : ∀ {a₁ a₂ b₂ b₁ aᵣ bᵣ}
          {A₁ : ★ a₁} {A₂ : ★ a₂}
          {B₁ : ★ b₁} {B₂ : ★ b₂}
          (Aᵣ : A₁ → A₂ → ★ aᵣ)
          (Bᵣ : B₁ → B₂ → ★ bᵣ)
          (p₁ : A₁ × B₁) (p₂ : A₂ × B₂) → ★ (aᵣ ⊔ bᵣ)
_⟦×⟧_ Aᵣ Bᵣ = ⟦Σ⟧ Aᵣ (λ _ → Bᵣ)

{-
_⟦×⟧_ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
          {b₁ b₂ bᵣ} {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : B₁ → B₂ → ★ bᵣ)
          (p₁ : A₁ × B₁) (p₂ : A₂ × B₂) → ★ _
_⟦×⟧_ Aᵣ Bᵣ = λ p₁ p₂ → Aᵣ (proj₁ p₁) (proj₁ p₂) ×
                        Bᵣ (proj₂ p₁) (proj₂ p₂)
-}

{- One can give these two types to ⟦_,_⟧:

⟦_,_⟧' : ∀ {a₁ a₂ b₁ b₂ aᵣ bᵣ}
       {A₁ : ★ a₁} {A₂ : ★ a₂}
       {B₁ : A₁ → ★ b₁} {B₂ : A₂ → ★ b₂}
       {Aᵣ : ⟦★⟧ aᵣ A₁ A₂}
       {Bᵣ : ⟦Pred⟧ Aᵣ bᵣ B₁ B₂}
       {x₁ x₂ y₁ y₂}
       (xᵣ : Aᵣ x₁ x₂)
       (yᵣ : Bᵣ xᵣ y₁ y₂)
     → ⟦Σ⟧ Aᵣ Bᵣ (x₁ , y₁) (x₂ , y₂)
⟦_,_⟧' = ⟦_,_⟧

⟦_,_⟧'' : ∀ {a₁ a₂ b₁ b₂ aᵣ bᵣ}
       {A₁ : ★ a₁} {A₂ : ★ a₂}
       {B₁ : A₁ → ★ b₁} {B₂ : A₂ → ★ b₂}
       {Aᵣ : ⟦★⟧ aᵣ A₁ A₂}
       {Bᵣ : ⟦Pred⟧ Aᵣ bᵣ B₁ B₂}
       {p₁ p₂}
       (⟦proj₁⟧ : Aᵣ (proj₁ p₁) (proj₁ p₂))
       (⟦proj₂⟧ : Bᵣ ⟦proj₁⟧ (proj₂ p₁) (proj₂ p₂))
     → ⟦Σ⟧ Aᵣ Bᵣ p₁ p₂
⟦_,_⟧'' = ⟦_,_⟧
-}

dec⟦Σ⟧ : ∀ {a₁ a₂ b₁ b₂ aᵣ bᵣ A₁ A₂ B₁ B₂}
       {Aᵣ : ⟦★⟧ {a₁} {a₂} aᵣ A₁ A₂}
       {Bᵣ : ⟦Pred⟧ {b₁} {b₂} bᵣ Aᵣ B₁ B₂}
       (decAᵣ : Dec⟦★⟧ Aᵣ)
       -- (substAᵣ : ∀ {x y ℓ} {p q} (P : Aᵣ x y → ★ ℓ) → P p → P q)
       (uniqAᵣ : ∀ {x y} (p q : Aᵣ x y) → p ≡ q)
       (decBᵣ : Dec⟦Pred⟧ Aᵣ {_} {_} {bᵣ {-BUG: with _ here Agda loops-}} Bᵣ)
     → Dec⟦★⟧ (⟦Σ⟧ Aᵣ Bᵣ)
dec⟦Σ⟧ {Bᵣ = Bᵣ} decAᵣ uniqAᵣ decBᵣ (x₁ , y₁) (x₂ , y₂) with decAᵣ x₁ x₂
... | no ¬xᵣ = no (¬xᵣ ∘ ⟦proj₁⟧)
... | yes xᵣ with decBᵣ xᵣ y₁ y₂
...           | yes yᵣ = yes (xᵣ ⟦,⟧ yᵣ)
...           | no ¬yᵣ = no (¬yᵣ ∘ f ∘ ⟦proj₂⟧)
  where f : ∀ {xᵣ'} → Bᵣ xᵣ' y₁ y₂ → Bᵣ xᵣ y₁ y₂
        f {xᵣ'} yᵣ rewrite uniqAᵣ xᵣ' xᵣ = yᵣ

module Dec₂ where
  map₂′ : ∀ {p₁ p₂ q} {P₁ : ★ p₁} {P₂ : ★ p₂} {Q : ★ q}
          → (P₁ → P₂ → Q) → (Q → P₁) → (Q → P₂) → Dec P₁ → Dec P₂ → Dec Q
  map₂′ _   π₁  _   (no ¬p₁)  _         = no (¬p₁ ∘ π₁)
  map₂′ _   _   π₂  _         (no ¬p₂)  = no (¬p₂ ∘ π₂)
  map₂′ mk  _   _   (yes p₁)  (yes p₂)  = yes (mk p₁ p₂)

dec⟦×⟧ : ∀ {a₁ a₂ b₁ b₂ aᵣ bᵣ}
           {A₁ : ★ a₁} {A₂ : ★ a₂}
           {B₁ : ★ b₁} {B₂ : ★ b₂}
           {Aᵣ : ⟦★⟧ aᵣ A₁ A₂}
           {Bᵣ : ⟦★⟧ bᵣ B₁ B₂}
           (decAᵣ : Dec⟦★⟧ Aᵣ)
           (decBᵣ : Dec⟦★⟧ Bᵣ)
         → Dec⟦★⟧ (Aᵣ ⟦×⟧ Bᵣ)
dec⟦×⟧ decAᵣ decBᵣ (x₁ , y₁) (x₂ , y₂) with decAᵣ x₁ x₂
... | no ¬xᵣ = no (¬xᵣ ∘ ⟦proj₁⟧)
... | yes xᵣ with decBᵣ y₁ y₂
...           | yes yᵣ = yes (xᵣ ⟦,⟧ yᵣ)
...           | no ¬yᵣ = no (¬yᵣ ∘ ⟦proj₂⟧)

mkΣ≡ : ∀ {a b} {A : ★ a} {x y : A} (B : A → ★ b) {p : B x} {q : B y} (xy : x ≡ y) → subst B xy p ≡ q → (x Σ., p) ≡ (y , q)
mkΣ≡ _ xy h rewrite xy | h = ≡.refl

Σ,-injective₁ : ∀ {a b} {A : ★ a} {B : A → ★ b} {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂} → (x₁ , y₁) ≡ (x₂ , y₂) → x₁ ≡ x₂
Σ,-injective₁ = ap proj₁

proj₁-injective : ∀ {a b} {A : ★ a} {B : A → ★ b} {x y : Σ A B}
                    (B-uniq : ∀ {z} (p₁ p₂ : B z) → p₁ ≡ p₂)
                  → proj₁ x ≡ proj₁ y → x ≡ y
proj₁-injective {x = (a , p₁)} {y = (_ , p₂)} B-uniq eq rewrite sym eq
  = cong (λ p → (a , p)) (B-uniq p₁ p₂)

proj₂-irrelevance : ∀ {a b} {A : ★ a} {B C : A → ★ b} {x₁ x₂ : A}
                      {y₁ : B x₁} {y₂ : B x₂} {z₁ : C x₁} {z₂ : C x₂}
                    → (C-uniq : ∀ {z} (p₁ p₂ : C z) → p₁ ≡ p₂)
                    → (x₁ , y₁) ≡ (x₂ , y₂)
                    → (x₁ , z₁) ≡ (x₂ , z₂)
proj₂-irrelevance C-uniq = proj₁-injective C-uniq ∘ Σ,-injective₁

≟Σ' : ∀ {A : ★₀} {P : A → ★₀}
       (decA : Decidable {A = A} _≡_)
       (uniqP : ∀ {x} (p q : P x) → p ≡ q)
     → Decidable {A = Σ A P} _≡_
≟Σ' decA uniqP (w₁ , p₁) (w₂ , p₂) with decA w₁ w₂
≟Σ' decA uniqP (w  , p₁) (.w , p₂) | yes refl
  = yes (cong (λ p → (w , p)) (uniqP p₁ p₂))
≟Σ' decA uniqP (w₁ , p₁) (w₂ , p₂) | no w≢ = no (w≢ ∘ cong proj₁)

proj₁-Injection : ∀ {a b} {A : ★ a} {B : A →  ★ b}
                  → (∀ {x} (p₁ p₂ : B x) → p₁ ≡ p₂)
                  → Injection (setoid (Σ A B))
                              (setoid A)
proj₁-Injection {B = B} B-uniq
     = record { to        = →-to-⟶ (proj₁ {B = B})
              ; injective = proj₁-injective B-uniq
              }

Δ : ∀ {a} {A : ★ a} → A → A × A
Δ x = x , x
