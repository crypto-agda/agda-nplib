module Data.Product.Param.Binary.NP where

open import Type using (★_)
open import Type.Param.Binary
open import Function.NP
open import Function.Param.Binary
open import Data.Product.NP
open import Data.Product.Param.Binary public
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

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

dec⟦Σ⟧ : ∀ {a₁ a₂ b₁ b₂ aᵣ bᵣ A₁ A₂ B₁ B₂}
       {Aᵣ : ⟦★⟧ {a₁} {a₂} aᵣ A₁ A₂}
       {Bᵣ : ⟦Pred⟧ {b₁} {b₂} bᵣ Aᵣ B₁ B₂}
       (decAᵣ : Dec⟦★⟧ Aᵣ)
       -- (substAᵣ : ∀ {x y ℓ} {p q} (P : Aᵣ x y → ★ ℓ) → P p → P q)
       (uniqAᵣ : ∀ {x y} (p q : Aᵣ x y) → p ≡ q)
       (decBᵣ : Dec⟦Pred⟧ Aᵣ {_} {_} {bᵣ {-BUG: with _ here Agda loops-}} Bᵣ)
     → Dec⟦★⟧ (⟦Σ⟧ Aᵣ Bᵣ)
dec⟦Σ⟧ {Bᵣ = Bᵣ} decAᵣ uniqAᵣ decBᵣ (x₁ , y₁) (x₂ , y₂) with decAᵣ x₁ x₂
... | no ¬xᵣ = no (¬xᵣ ∘ ⟦fst⟧)
... | yes xᵣ with decBᵣ xᵣ y₁ y₂
...           | yes yᵣ = yes (xᵣ ⟦,⟧ yᵣ)
...           | no ¬yᵣ = no (¬yᵣ ∘ f ∘ ⟦snd⟧)
  where f : ∀ {xᵣ'} → Bᵣ xᵣ' y₁ y₂ → Bᵣ xᵣ y₁ y₂
        f {xᵣ'} yᵣ rewrite uniqAᵣ xᵣ' xᵣ = yᵣ

dec⟦×⟧ : ∀ {a₁ a₂ b₁ b₂ aᵣ bᵣ}
           {A₁ : ★ a₁} {A₂ : ★ a₂}
           {B₁ : ★ b₁} {B₂ : ★ b₂}
           {Aᵣ : ⟦★⟧ aᵣ A₁ A₂}
           {Bᵣ : ⟦★⟧ bᵣ B₁ B₂}
           (decAᵣ : Dec⟦★⟧ Aᵣ)
           (decBᵣ : Dec⟦★⟧ Bᵣ)
         → Dec⟦★⟧ (Aᵣ ⟦×⟧ Bᵣ)
dec⟦×⟧ decAᵣ decBᵣ (x₁ , y₁) (x₂ , y₂) with decAᵣ x₁ x₂
... | no ¬xᵣ = no (¬xᵣ ∘ ⟦fst⟧)
... | yes xᵣ with decBᵣ y₁ y₂
...           | yes yᵣ = yes (xᵣ ⟦,⟧ yᵣ)
...           | no ¬yᵣ = no (¬yᵣ ∘ ⟦snd⟧)
