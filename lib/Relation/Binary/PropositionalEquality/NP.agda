{-# OPTIONS --without-K #-}
-- move this to propeq
module Relation.Binary.PropositionalEquality.NP where

open import Type hiding (★)
open import Data.One using (𝟙)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality public hiding (module ≡-Reasoning; subst) renaming (cong₂ to ap₂)
open import Relation.Binary.NP
open import Relation.Binary.Bijection
open import Relation.Binary.Logical
open import Relation.Nullary

private
  module Dummy {a} {A : ★ a} where
    open IsEquivalence (isEquivalence {a} {A}) public hiding (refl; sym; trans)
open Dummy public

PathOver : ∀ {i j} {A : ★ i} (B : A → ★ j)
  {x y : A} (p : x ≡ y) (u : B x) (v : B y) → ★ j
PathOver B refl u v = (u ≡ v)

syntax PathOver B p u v =
  u ≡ v [ B ↓ p ]

{- one day this will work -}
-- pattern idp = refl

-- Some definitions with the names from Agda-HoTT
-- this is only a temporary state of affairs...
module _ {a} {A : ★ a} where

    idp : {x : A} → x ≡ x
    idp = refl

    infixr 8 _∙_ _∙'_

    _∙_ _∙'_ : {x y z : A} → (x ≡ y → y ≡ z → x ≡ z)

    refl ∙ q  = q
    q ∙' refl = q

    !_ : {x y : A} → (x ≡ y → y ≡ x)
    !_ refl = refl

ap↓ : ∀ {i j k} {A : ★ i} {B : A → ★ j} {C : A → ★ k}
  (g : {a : A} → B a → C a) {x y : A} {p : x ≡ y}
  {u : B x} {v : B y}
  → (u ≡ v [ B ↓ p ] → g u ≡ g v [ C ↓ p ])
ap↓ g {p = refl} refl = refl

ap : ∀ {i j} {A : ★ i} {B : ★ j} (f : A → B) {x y : A}
  → (x ≡ y → f x ≡ f y)
ap f p = ap↓ {A = 𝟙} f {p = refl} p

apd : ∀ {i j} {A : ★ i} {B : A → ★ j} (f : (a : A) → B a) {x y : A}
  → (p : x ≡ y) → f x ≡ f y [ B ↓ p ]
apd f refl = refl

coe : ∀ {i} {A B : ★ i} (p : A ≡ B) → A → B
coe refl x = x

coe! : ∀ {i} {A B : ★ i} (p : A ≡ B) → B → A
coe! p = coe (! p)

module _ {ℓ ℓp}
         {A : Set ℓ}
         (P : A → Set ℓp)
         {x y : A}
         where
    tr : (p : x ≡ y) → P x → P y
    tr p = coe (ap P p)

    tr! : (p : y ≡ x) → P x → P y
    tr! p = tr (! p)

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) {a₀ a₁ b₀ b₁ c₀ c₁}
        → a₀ ≡ a₁ → b₀ ≡ b₁ → c₀ ≡ c₁ → f a₀ b₀ c₀ ≡ f a₁ b₁ c₁
cong₃ f refl refl refl = refl

_≗₂_ : ∀ {a b c} {A : ★ a} {B : ★ b} {C : ★ c} (f g : A → B → C) → ★ _
f ≗₂ g = ∀ x y → f x y ≡ g x y

module _ {a} {A : ★ a} where
  J-orig : ∀ {b} (P : (x y : A) → x ≡ y → ★_ b) → (∀ x → P x x refl) → ∀ {x y} (p : x ≡ y) → P x y p
  J-orig P p refl = p _

  -- This version is better suited to our identity type which has the first argument as a parameter.
  -- (due to Paulin-Mohring)
  J : ∀ {b} {x : A} (P : (y : A) → x ≡ y → ★_ b) → P x refl → ∀ {y} (p : x ≡ y) → P y p
  J P p refl = p

  injective : InjectiveRel A _≡_
  injective p q = p ∙ ! q

  surjective : SurjectiveRel A _≡_
  surjective p q = ! p ∙ q

  bijective : BijectiveRel A _≡_
  bijective = record { injectiveREL = injective; surjectiveREL = surjective }

  Equalizer : ∀ {b} {B : A → ★ b} (f g : (x : A) → B x) → ★ _
  Equalizer f g = Σ A (λ x → f x ≡ g x)
  {- In a category theory context this type would the object 'E'
     and 'fst' would be the morphism 'eq : E → A' such that
     given any object O, and morphism 'm : O → A', there exists
     a unique morphism 'u : O → E' such that 'eq ∘ u ≡ m'.
  -}

  Pullback : ∀ {b c} {B : ★ b} {C : ★ c} (f : A → C) (g : B → C) → ★ _
  Pullback {B = B} f g = Σ A (λ x → Σ B (λ y → f x ≡ g y))

module ≡-Reasoning {a} {A : ★ a} where
  open Setoid-Reasoning (setoid A) public
    renaming (_≈⟨_⟩_ to _≡⟨_⟩_;
                    _≈⟨by-definition⟩_ to _≡⟨by-definition⟩_)

module ≗-Reasoning {a b} {A : ★ a} {B : ★ b} where
  open Setoid-Reasoning (A →-setoid B) public
    renaming (_≈⟨_⟩_ to _≗⟨_⟩_;
                    _≈⟨by-definition⟩_ to _≗⟨by-definition⟩_)

data ⟦≡⟧ {a₀ a₁ aᵣ}
         {A₀ A₁} (Aᵣ : ⟦★⟧ {a₀} {a₁} aᵣ A₀ A₁)
         {x₀ x₁} (xᵣ : Aᵣ x₀ x₁)
       : (Aᵣ ⟦→⟧ ⟦★⟧ aᵣ) (_≡_ x₀) (_≡_ x₁) where
    -- : ∀ {y₀ y₁} (yᵣ : Aᵣ y₀ y₁) → x₀ ≡ y₀ → x₁ ≡ y₁ → ★
  ⟦refl⟧ : ⟦≡⟧ Aᵣ xᵣ xᵣ refl refl

-- Double checking level 0 with a direct ⟦_⟧ encoding
private
  ⟦≡⟧′ : (∀⟨ Aᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ ⟦★₀⟧) _≡_ _≡_
  ⟦≡⟧′ = ⟦≡⟧

  ⟦refl⟧′ : (∀⟨ Aᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ ∀⟨ xᵣ ∶ Aᵣ ⟩⟦→⟧ ⟦≡⟧ Aᵣ xᵣ xᵣ) refl refl
  ⟦refl⟧′ _ _ = ⟦refl⟧
