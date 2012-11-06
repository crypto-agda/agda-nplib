{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.Logical where

open import Type
open import Level

⟦★⟧ : ∀ {a₁ a₂} aᵣ (A₁ : Set a₁) (A₂ : Set a₂) → Set _
⟦★⟧ aᵣ A₁ A₂ = A₁ → A₂ → Set aᵣ

⟦★₀⟧ : ∀ (A₁ A₂ : ★) → ★₁
⟦★₀⟧ = ⟦★⟧ zero

⟦★₁⟧ : ∀ (A₁ A₂ : ★₁) → ★₂
⟦★₁⟧ = ⟦★⟧ (suc zero)

-- old name
⟦Set⟧ : ∀ {a₁ a₂} aᵣ (A₁ : Set a₁) (A₂ : Set a₂) → Set _
⟦Set⟧ aᵣ A₁ A₂ = A₁ → A₂ → Set aᵣ

-- old name
⟦Set₀⟧ : ∀ (A₁ A₂ : Set) → Set₁
⟦Set₀⟧ = ⟦★₀⟧

-- old name
⟦Set₁⟧ : ∀ (A₁ A₂ : Set₁) → Set₂
⟦Set₁⟧ = ⟦★₁⟧

⟦Π⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ)
         {b₁ b₂ bᵣ} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂} (Bᵣ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → B₁ x₁ → B₂ x₂ → Set bᵣ)
         (f₁ : (x : A₁) → B₁ x) (f₂ : (x : A₂) → B₂ x) → Set _
⟦Π⟧ Aᵣ Bᵣ = λ f₁ f₂ → ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → Bᵣ xᵣ (f₁ x₁) (f₂ x₂)

infixr 0 ⟦Π⟧
syntax ⟦Π⟧ Aᵣ (λ xᵣ → f) = ⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ f

⟦Π⟧e : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ)
         {b₁ b₂ bᵣ} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂} (Bᵣ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → B₁ x₁ → B₂ x₂ → Set bᵣ)
         (f₁ : (x : A₁) → B₁ x) (f₂ : (x : A₂) → B₂ x) → Set _
⟦Π⟧e Aᵣ Bᵣ = λ f₁ f₂ → ∀ x₁ x₂ (xᵣ : Aᵣ x₁ x₂) → Bᵣ xᵣ (f₁ x₁) (f₂ x₂)

⟦∀⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ)
         {b₁ b₂ bᵣ} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂} (Bᵣ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → B₁ x₁ → B₂ x₂ → Set bᵣ)
         (f₁ : {x : A₁} → B₁ x) (f₂ : {x : A₂} → B₂ x) → Set _
⟦∀⟧ Aᵣ Bᵣ = λ f₁ f₂ → ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → Bᵣ xᵣ (f₁ {x₁}) (f₂ {x₂})

infixr 0 ⟦∀⟧
syntax ⟦∀⟧ Aᵣ (λ xᵣ → f) = ∀⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ f

infixr 1 _⟦→⟧_
_⟦→⟧_ : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ)
          {b₁ b₂ bᵣ} {B₁ : Set b₁} {B₂ : Set b₂} (Bᵣ : B₁ → B₂ → Set bᵣ)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → Set _
Aᵣ ⟦→⟧ Bᵣ = ⟦Π⟧ Aᵣ (λ _ → Bᵣ)

infixr 0 _⟦→⟧e_
_⟦→⟧e_ : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ)
          {b₁ b₂ bᵣ} {B₁ : Set b₁} {B₂ : Set b₂} (Bᵣ : B₁ → B₂ → Set bᵣ)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → Set _
_⟦→⟧e_ Aᵣ Bᵣ = ⟦Π⟧e Aᵣ (λ _ → Bᵣ)

open import Data.Product


open import Data.Unit

record ⟦⊤⟧ (x₁ x₂ : ⊤) : ★ where
  constructor ⟦tt⟧

open import Data.Empty

data ⟦⊥⟧ (x₁ x₂ : ⊥) : ★ where

open import Relation.Nullary

infix 3 ⟦¬⟧_

--⟦¬⟧_ : (⟦★⟧ ⟦→⟧ ⟦★⟧) ¬_ ¬_
⟦¬⟧_ : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ) → ¬ A₁ → ¬ A₂ → Set _
⟦¬⟧ Aᵣ = Aᵣ ⟦→⟧ ⟦⊥⟧

{-
⟦∃⟧ : {A₁ A₂ : World → ★} (Aᵣ : ∀ {α₁ α₂} → ⟦World⟧ α₁ α₂ → A₁ α₁ → A₂ α₂ → ★)
       (p₁ : ∃ A₁) (f₂ : ∃ A₂) → ★
⟦∃⟧ Aᵣ = λ p₁ p₂ → Σ[ αᵣ ∶ ⟦World⟧ (proj₁ p₁) (proj₁ p₂) ]
                       (Aᵣ αᵣ (proj₂ p₁) (proj₂ p₂))

syntax ⟦∃⟧ (λ αᵣ → f) = ⟦∃⟧[ αᵣ ] f
-}

Pred : ∀ ℓ {a} (A : Set a) → Set (a ⊔ suc ℓ)
Pred ℓ A = A → Set ℓ

⟦Pred⟧ : ∀ {p₁ p₂} pᵣ {a₁ a₂ aᵣ} → (⟦★⟧ {a₁} {a₂} aᵣ ⟦→⟧ ⟦★⟧ _) (Pred p₁) (Pred p₂)
--⟦Pred⟧ {p₁} {p₂} pᵣ Aᵣ = Aᵣ ⟦→⟧ ⟦★⟧ (p₁ ⊔ p₂ ⊔ pᵣ)
⟦Pred⟧ {p₁} {p₂} pᵣ Aᵣ = λ f₁ f₂ → ∀ {x₁} {x₂} (xᵣ : Aᵣ x₁ x₂) → f₁ x₁ → f₂ x₂ → Set (p₁ ⊔ p₂ ⊔ pᵣ)

open import Relation.Binary

private
  REL′ : ∀ ℓ {a b} → Set a → Set b → Set (a ⊔ b ⊔ suc ℓ)
  REL′ ℓ A B = A → B → Set ℓ

  ⟦REL⟧′ : ∀ {a₁ a₂ aᵣ b₁ b₂ bᵣ ℓ₁ ℓ₂} ℓᵣ →
          (⟦★⟧ {a₁} {a₂} aᵣ ⟦→⟧ ⟦★⟧ {b₁} {b₂} bᵣ ⟦→⟧ ⟦★⟧ _) (REL′ ℓ₁) (REL′ ℓ₂)
  ⟦REL⟧′ ℓᵣ Aᵣ Bᵣ = Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ (⟦★⟧ ℓᵣ)

⟦REL⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ)
          {b₁ b₂ bᵣ} {B₁ : Set b₁} {B₂ : Set b₂} (Bᵣ : B₁ → B₂ → Set bᵣ)
          {ℓ₁ ℓ₂} ℓᵣ (∼₁ : REL A₁ B₁ ℓ₁) (∼₂ : REL A₂ B₂ ℓ₂) → Set _
⟦REL⟧ Aᵣ Bᵣ ℓᵣ = Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ (⟦★⟧ ℓᵣ)

⟦Rel⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ)
          {ℓ₁ ℓ₂} ℓᵣ (∼₁ : Rel A₁ ℓ₁) (∼₂ : Rel A₂ ℓ₂) → Set _
⟦Rel⟧ Aᵣ ℓᵣ = ⟦REL⟧ Aᵣ Aᵣ ℓᵣ

-- data ⟦Dec⟧ {ℓ₁ ℓ₂ ℓᵣ} {P₁ : Set ℓ₁} {P₂ : Set ℓ₂} (Pᵣ : P₁ → P₂ → Set ℓᵣ) : Dec P₁ → Dec P₂ → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓᵣ) where
-- data ⟦Dec⟧ {ℓᵣ} : ⟦Pred⟧ (⟦★⟧ ℓᵣ) ℓᵣ Dec Dec where
data ⟦Dec⟧ {ℓ₁ ℓ₂ ℓᵣ} {P₁ : Set ℓ₁} {P₂ : Set ℓ₂} (Pᵣ : P₁ → P₂ → Set ℓᵣ) : ⟦★⟧ (ℓ₁ ⊔ ℓ₂ ⊔ ℓᵣ) (Dec P₁) (Dec P₂) where
  yes : {-∀ {P₁ P₂ Pᵣ}-} {p₁ : P₁} {p₂ : P₂} (pᵣ : Pᵣ p₁ p₂) → ⟦Dec⟧ Pᵣ (yes p₁) (yes p₂)
  no  : {-∀ {P₁ P₂ Pᵣ}-} {¬p₁ : ¬ P₁} {¬p₂ : ¬ P₂} (¬pᵣ : (⟦¬⟧ Pᵣ) ¬p₁ ¬p₂) → ⟦Dec⟧ Pᵣ (no ¬p₁) (no ¬p₂)

--⟦Decidable⟧ : ∀ {a₁ a₂ aᵣ b₁ b₂ bᵣ ℓ₁ ℓ₂ ℓᵣ} → (∀⟨ Aᵣ ∶ ⟦★⟧ {a₁} {a₂} aᵣ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ {b₁ b₂} bᵣ ⟩⟦→⟧ ⟦REL⟧ Aᵣ Bᵣ {ℓ₁} {ℓ₂} ℓᵣ ⟦→⟧ ⟦★⟧ _) Decidable Decidable
⟦Decidable⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : Set a₁} {A₂ : Set a₂} (Aᵣ : A₁ → A₂ → Set aᵣ)
                 {b₁ b₂ bᵣ} {B₁ : Set b₁} {B₂ : Set b₂} (Bᵣ : B₁ → B₂ → Set bᵣ)
                 {ℓ₁ ℓ₂ ℓᵣ} {∼₁ : REL A₁ B₁ ℓ₁} {∼₂ : REL A₂ B₂ ℓ₂} (∼ᵣ : ⟦REL⟧ Aᵣ Bᵣ ℓᵣ ∼₁ ∼₂)
              → Decidable ∼₁ → Decidable ∼₂ → Set _
⟦Decidable⟧ Aᵣ Bᵣ _∼ᵣ_ = ⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ ⟨ yᵣ ∶ Bᵣ ⟩⟦→⟧ ⟦Dec⟧ (xᵣ ∼ᵣ yᵣ)

