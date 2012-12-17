{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.Logical where

open import Type hiding (★)
open import Level
open import Algebra.FunctionProperties
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Unary.NP hiding (Decidable)
open import Relation.Binary

⟦★⟧ : ∀ {a₁ a₂} aᵣ (A₁ : ★ a₁) (A₂ : ★ a₂) → ★ _
⟦★⟧ aᵣ A₁ A₂ = A₁ → A₂ → ★ aᵣ

⟦★⟧₀ : ∀ {a₁ a₂} (A₁ : ★ a₁) (A₂ : ★ a₂) → ★ _
⟦★⟧₀ = ⟦★⟧ zero

⟦★₀⟧ : ∀ (A₁ A₂ : ★₀) → ★₁
⟦★₀⟧ = ⟦★⟧₀

⟦★₁⟧ : ∀ (A₁ A₂ : ★₁) → ★₂
⟦★₁⟧ = ⟦★⟧ (suc zero)

-- old name
⟦Set⟧ : ∀ {a₁ a₂} aᵣ (A₁ : ★ a₁) (A₂ : ★ a₂) → ★ _
⟦Set⟧ aᵣ A₁ A₂ = A₁ → A₂ → ★ aᵣ

-- old name
⟦Set₀⟧ : ∀ (A₁ A₂ : Set) → Set₁
⟦Set₀⟧ = ⟦★₀⟧

-- old name
⟦Set₁⟧ : ∀ (A₁ A₂ : Set₁) → Set₂
⟦Set₁⟧ = ⟦★₁⟧

⟦Π⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
         {b₁ b₂ bᵣ} {B₁ : A₁ → ★ b₁} {B₂ : A₂ → ★ b₂} (Bᵣ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → B₁ x₁ → B₂ x₂ → ★ bᵣ)
         (f₁ : (x : A₁) → B₁ x) (f₂ : (x : A₂) → B₂ x) → ★ _
⟦Π⟧ Aᵣ Bᵣ = λ f₁ f₂ → ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → Bᵣ xᵣ (f₁ x₁) (f₂ x₂)

infixr 0 ⟦Π⟧
syntax ⟦Π⟧ Aᵣ (λ xᵣ → f) = ⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ f

⟦Π⟧e : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
         {b₁ b₂ bᵣ} {B₁ : A₁ → ★ b₁} {B₂ : A₂ → ★ b₂} (Bᵣ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → B₁ x₁ → B₂ x₂ → ★ bᵣ)
         (f₁ : (x : A₁) → B₁ x) (f₂ : (x : A₂) → B₂ x) → ★ _
⟦Π⟧e Aᵣ Bᵣ = λ f₁ f₂ → ∀ x₁ x₂ (xᵣ : Aᵣ x₁ x₂) → Bᵣ xᵣ (f₁ x₁) (f₂ x₂)

⟦∀⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
         {b₁ b₂ bᵣ} {B₁ : A₁ → ★ b₁} {B₂ : A₂ → ★ b₂} (Bᵣ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → B₁ x₁ → B₂ x₂ → ★ bᵣ)
         (f₁ : {x : A₁} → B₁ x) (f₂ : {x : A₂} → B₂ x) → ★ _
⟦∀⟧ Aᵣ Bᵣ = λ f₁ f₂ → ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → Bᵣ xᵣ (f₁ {x₁}) (f₂ {x₂})

infixr 0 ⟦∀⟧
syntax ⟦∀⟧ Aᵣ (λ xᵣ → f) = ∀⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ f

infixr 1 _⟦→⟧_
_⟦→⟧_ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
          {b₁ b₂ bᵣ} {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : B₁ → B₂ → ★ bᵣ)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → ★ _
Aᵣ ⟦→⟧ Bᵣ = ⟦Π⟧ Aᵣ (λ _ → Bᵣ)

infixr 0 _⟦→⟧e_
_⟦→⟧e_ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
          {b₁ b₂ bᵣ} {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : B₁ → B₂ → ★ bᵣ)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → ★ _
_⟦→⟧e_ Aᵣ Bᵣ = ⟦Π⟧e Aᵣ (λ _ → Bᵣ)

record ⟦⊤⟧ (x₁ x₂ : ⊤) : ★₀ where
  constructor ⟦tt⟧

data ⟦⊥⟧ (x₁ x₂ : ⊥) : ★₀ where

infix 3 ⟦¬⟧_

⟦¬⟧_ : ∀ {a₁ a₂ aₚ} → (⟦★⟧ {a₁} {a₂} aₚ ⟦→⟧ ⟦★⟧ _) ¬_ ¬_
⟦¬⟧ Aᵣ = Aᵣ ⟦→⟧ ⟦⊥⟧

-- Products ⟦Σ⟧, ⟦∃⟧, ⟦×⟧ are in Data.Product.NP

⟦Pred⟧ : ∀ {p₁ p₂} pᵣ {a₁ a₂ aᵣ} → (⟦★⟧ {a₁} {a₂} aᵣ ⟦→⟧ ⟦★⟧ _) (Pred p₁) (Pred p₂)
⟦Pred⟧ pᵣ Aᵣ = Aᵣ ⟦→⟧ ⟦★⟧ pᵣ

private
  REL′ : ∀ ℓ {a b} → ★ a → ★ b → ★ (a ⊔ b ⊔ suc ℓ)
  REL′ ℓ A B = A → B → ★ ℓ

  ⟦REL⟧′ : ∀ {a₁ a₂ aᵣ b₁ b₂ bᵣ r₁ r₂} rᵣ →
          (⟦★⟧ {a₁} {a₂} aᵣ ⟦→⟧ ⟦★⟧ {b₁} {b₂} bᵣ ⟦→⟧ ⟦★⟧ _) (REL′ r₁) (REL′ r₂)
  ⟦REL⟧′ rᵣ Aᵣ Bᵣ = Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ (⟦★⟧ rᵣ)

⟦REL⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
          {b₁ b₂ bᵣ} {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : B₁ → B₂ → ★ bᵣ)
          {r₁ r₂} rᵣ (∼₁ : REL A₁ B₁ r₁) (∼₂ : REL A₂ B₂ r₂) → ★ _
⟦REL⟧ Aᵣ Bᵣ rᵣ = Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ (⟦★⟧ rᵣ)

⟦Rel⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : A₁ → A₂ → ★ aᵣ)
          {r₁ r₂} ℓᵣ (∼₁ : Rel A₁ r₁) (∼₂ : Rel A₂ r₂) → ★ _
⟦Rel⟧ Aᵣ rᵣ = ⟦REL⟧ Aᵣ Aᵣ rᵣ

data ⟦Dec⟧ {ℓ₁ ℓ₂ ℓᵣ} {P₁ : ★ ℓ₁} {P₂ : ★ ℓ₂} (Pᵣ : P₁ → P₂ → ★ ℓᵣ) : ⟦★⟧ (ℓ₁ ⊔ ℓ₂ ⊔ ℓᵣ) (Dec P₁) (Dec P₂) where
  yes : {p₁ : P₁} {p₂ : P₂} (pᵣ : Pᵣ p₁ p₂) → ⟦Dec⟧ Pᵣ (yes p₁) (yes p₂)
  no  : {¬p₁ : ¬ P₁} {¬p₂ : ¬ P₂} (¬pᵣ : (⟦¬⟧ Pᵣ) ¬p₁ ¬p₂) → ⟦Dec⟧ Pᵣ (no ¬p₁) (no ¬p₂)

private
  ⟦Dec⟧' : ∀ {p₁} {p₂} {pᵣ} → ⟦Pred⟧ {p₁} {p₂} _ (⟦★⟧ pᵣ) Dec Dec
  ⟦Dec⟧' = ⟦Dec⟧

⟦Decidable⟧ : ∀ {a₁ a₂ aᵣ b₁ b₂ bᵣ ℓ₁ ℓ₂ ℓᵣ}
              → (∀⟨ Aᵣ ∶ ⟦★⟧ {a₁} {a₂} aᵣ ⟩⟦→⟧
                 ∀⟨ Bᵣ ∶ ⟦★⟧ {b₁} {b₂} bᵣ ⟩⟦→⟧
                   ⟦REL⟧ Aᵣ Bᵣ {ℓ₁} {ℓ₂} ℓᵣ ⟦→⟧ ⟦★⟧ _) Decidable Decidable
⟦Decidable⟧ Aᵣ Bᵣ _∼ᵣ_ = ⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ ⟨ yᵣ ∶ Bᵣ ⟩⟦→⟧ ⟦Dec⟧ (xᵣ ∼ᵣ yᵣ)

⟦Op₁⟧ : ∀ {a} → (⟦★⟧ {a} {a} a ⟦→⟧ ⟦★⟧ a) Op₁ Op₁
⟦Op₁⟧ Aᵣ = Aᵣ ⟦→⟧ Aᵣ

⟦Op₂⟧ : ∀ {a} → (⟦★⟧ {a} {a} a ⟦→⟧ ⟦★⟧ a) Op₂ Op₂
⟦Op₂⟧ Aᵣ = Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ Aᵣ

open import Function.Equivalence
private
  ⟦→⟧⇔Preserves :
    ∀ {a b aᵣ bᵣ}
      {A : ★ a} {B : ★ b}
      {Aᵣ : ⟦★⟧ aᵣ A A}
      {Bᵣ : ⟦★⟧ bᵣ B B}
      {f}
    → (Aᵣ ⟦→⟧ Bᵣ) f f ⇔ f Preserves Aᵣ ⟶ Bᵣ

  ⟦→⟧⇔Preserves = equivalence (λ x → x) (λ x → x)

  ⟦→⟧²⇔Preserves₂ :
    ∀ {a b c aᵣ bᵣ cᵣ}
      {A : ★ a} {B : ★ b} {C : ★ c}
      {Aᵣ : ⟦★⟧ aᵣ A A}
      {Bᵣ : ⟦★⟧ bᵣ B B}
      {Cᵣ : ⟦★⟧ cᵣ C C}
      {f}
    → (Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ Cᵣ) f f ⇔ f Preserves₂ Aᵣ ⟶ Bᵣ ⟶ Cᵣ

  ⟦→⟧²⇔Preserves₂ = equivalence (λ f {x} {y}   {_} {_} z → f {x} {y} z)
                                (λ f {x} {y} z {_} {_}   → f z)

⟦Inj⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : ⟦★⟧ aᵣ A₁ A₂)
          {b₁ b₂ bᵣ} {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : ⟦★⟧ bᵣ B₁ B₂)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → ★ _
⟦Inj⟧ Aᵣ Bᵣ f₁ f₂ = ∀ {x₁ x₂} (xᵣ : Bᵣ (f₁ x₁) (f₂ x₂)) → Aᵣ x₁ x₂

⟦Inj⟧′ : ∀ {a aᵣ} {A : ★ a} (Aᵣ : ⟦★⟧ aᵣ A A)
           {b bᵣ} {B : ★ b} (Bᵣ : ⟦★⟧ bᵣ B B)
           (f : A → B) → ★ _
⟦Inj⟧′ Aᵣ Bᵣ f = ⟦Inj⟧ Aᵣ Bᵣ f f
