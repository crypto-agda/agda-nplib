{-# OPTIONS --universe-polymorphism #-}
module Data.Sum.NP where

open import Type hiding (★)
open import Level
open import Function
open import Data.Sum public
open import Relation.Binary.Logical
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_;_≢_;_≗_)

inj₁-inj : ∀ {a b} {A : ★ a} {B : ★ b} {x y : A} → (inj₁ x ∶ A ⊎ B) ≡ inj₁ y → x ≡ y
inj₁-inj ≡.refl = ≡.refl

inj₂-inj : ∀ {a b} {A : ★ a} {B : ★ b} {x y : B} → (inj₂ x ∶ A ⊎ B) ≡ inj₂ y → x ≡ y
inj₂-inj ≡.refl = ≡.refl

infixr 4 _⟦⊎⟧_

data _⟦⊎⟧_ {a₁ a₂ b₁ b₂ aᵣ bᵣ}
            {A₁ : ★ a₁} {A₂ : ★ a₂}
            (Aᵣ : A₁ → A₂ → ★ aᵣ)
            {B₁ : ★ b₁} {B₂ : ★ b₂}
            (Bᵣ : B₁ → B₂ → ★ bᵣ) : A₁ ⊎ B₁ → A₂ ⊎ B₂ → ★ (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ aᵣ ⊔ bᵣ) where
  inj₁ : ∀ {x₁ x₂} (xᵣ : Aᵣ x₁ x₂) → (Aᵣ ⟦⊎⟧ Bᵣ) (inj₁ x₁) (inj₁ x₂)
  inj₂ : ∀ {x₁ x₂} (xᵣ : Bᵣ x₁ x₂) → (Aᵣ ⟦⊎⟧ Bᵣ) (inj₂ x₁) (inj₂ x₂)

⟦[_,_]′⟧ : ∀ {a b c} →
             (∀⟨ A ∶ ⟦★⟧ a ⟩⟦→⟧ ∀⟨ B ∶ ⟦★⟧ b ⟩⟦→⟧ ∀⟨ C ∶ ⟦★⟧ c ⟩⟦→⟧
                (A ⟦→⟧ C) ⟦→⟧ (B ⟦→⟧ C) ⟦→⟧ (A ⟦⊎⟧ B) ⟦→⟧ C)
             ([_,_]′ {a} {b} {c}) ([_,_]′ {a} {b} {c})
⟦[_,_]′⟧ _ _ _ f _ (inj₁ xᵣ) = f xᵣ
⟦[_,_]′⟧ _ _ _ _ g (inj₂ xᵣ) = g xᵣ

⟦map⟧ : ∀ {a b c d} →
        (∀⟨ A ∶ ⟦★⟧ a ⟩⟦→⟧ ∀⟨ B ∶ ⟦★⟧ b ⟩⟦→⟧ ∀⟨ C ∶ ⟦★⟧ c ⟩⟦→⟧ ∀⟨ D ∶ ⟦★⟧ d ⟩⟦→⟧
            (A ⟦→⟧ C) ⟦→⟧ (B ⟦→⟧ D) ⟦→⟧ (A ⟦⊎⟧ B ⟦→⟧ C ⟦⊎⟧ D))
        (map {a} {b} {c} {d}) (map {a} {b} {c} {d})
⟦map⟧ A B C D f g = ⟦[_,_]′⟧ A B (C ⟦⊎⟧ D) (inj₁ ∘′ f) (inj₂ ∘′ g)

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

open import Data.Bool
open import Data.Product
open import Function.Inverse
open import Function.LeftInverse
open ≡ using (→-to-⟶)

⊎-proj₁ : ∀ {a b} {A : ★ a} {B : ★ b} → A ⊎ B → Bool
⊎-proj₁ (inj₁ _) = true
⊎-proj₁ (inj₂ _) = false

⊎-proj₂ : ∀ {ℓ} {A B : ★ ℓ} (x : A ⊎ B) → if ⊎-proj₁ x then A else B
⊎-proj₂ (inj₁ x) = x
⊎-proj₂ (inj₂ x) = x

⊎⇿ΣBool : ∀ {ℓ} {A B : ★ ℓ} → (A ⊎ B) ↔ ∃ λ b → if b then A else B
⊎⇿ΣBool {A = A} {B} = record { to = →-to-⟶ to; from = →-to-⟶ from
                             ; inverse-of = record { left-inverse-of = left
                                                   ; right-inverse-of = right } }
  where
    to : A ⊎ B → ∃ λ b → if b then A else B
    to (inj₁ x) = true  , x
    to (inj₂ x) = false , x
    from : (∃ λ b → if b then A else B) → A ⊎ B
    from (true  , x) = inj₁ x
    from (false , x) = inj₂ x
    left : →-to-⟶ from LeftInverseOf →-to-⟶ to
    left (inj₁ x) = ≡.refl
    left (inj₂ x) = ≡.refl
    right : →-to-⟶ from RightInverseOf →-to-⟶ to
    right (true  , x) = ≡.refl
    right (false , x) = ≡.refl
