-- NOTE with-K
-- move this to propeq
module Relation.Binary.PropositionalEquality.NP where

open import Relation.Binary.PropositionalEquality public hiding (module ≡-Reasoning)
open import Relation.Binary.NP
open import Relation.Binary.Bijection
open import Relation.Binary.Logical
open import Relation.Nullary

private
  module Dummy {a} {A : Set a} where
    open IsEquivalence (isEquivalence {a} {A}) public hiding (refl; sym; trans)
open Dummy public

congD : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) {x y} (p : x ≡ y) → subst B p (f x) ≡ f y
congD f refl = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) {a₁ a₂ b₁ b₂ c₁ c₂}
        → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong₃ f refl refl refl = refl

_≡≡_ : ∀ {a} {A : Set a} {i j : A}
         (i≡j₁ : i ≡ j) (i≡j₂ : i ≡ j) → i≡j₁ ≡ i≡j₂
_≡≡_ refl refl = refl

_≟≡_ : ∀ {a} {A : Set a} {i j : A} → Decidable {A = i ≡ j} _≡_
_≟≡_ refl refl = yes refl

_≗₂_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f g : A → B → C) → Set _
f ≗₂ g = ∀ x y → f x y ≡ g x y

injective : ∀ {a} {A : Set a} → InjectiveRel A _≡_
injective refl refl = refl

surjective : ∀ {a} {A : Set a} → SurjectiveRel A _≡_
surjective refl refl = refl

bijective : ∀ {a} {A : Set a} → BijectiveRel A _≡_
bijective = record { injectiveREL = injective; surjectiveREL = surjective }

module ≡-Reasoning {a} {A : Set a} where
  open Setoid-Reasoning (setoid A) public renaming (_≈⟨_⟩_ to _≡⟨_⟩_)

module ≗-Reasoning {a b} {A : Set a} {B : Set b} where
  open Setoid-Reasoning (A →-setoid B) public renaming (_≈⟨_⟩_ to _≗⟨_⟩_)

data ⟦≡⟧ {a₁ a₂ aᵣ}
         {A₁ A₂} (Aᵣ : ⟦★⟧ {a₁} {a₂} aᵣ A₁ A₂)
         {x₁ x₂} (xᵣ : Aᵣ x₁ x₂)
       : (Aᵣ ⟦→⟧ ⟦★⟧ aᵣ) (_≡_ x₁) (_≡_ x₂) where
    -- : ∀ {y₁ y₂} (yᵣ : Aᵣ y₁ y₂) → x₁ ≡ y₁ → x₂ ≡ y₂ → ★
  ⟦refl⟧ : ⟦≡⟧ Aᵣ xᵣ xᵣ refl refl

-- Double checking level 0 with a direct ⟦_⟧ encoding
private
  ⟦≡⟧′ : (∀⟨ Aᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ ⟦★₀⟧) _≡_ _≡_
  ⟦≡⟧′ = ⟦≡⟧

  ⟦refl⟧′ : (∀⟨ Aᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ ∀⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ ⟦≡⟧ Aᵣ xᵣ xᵣ) refl refl
  ⟦refl⟧′ _ _ = ⟦refl⟧
