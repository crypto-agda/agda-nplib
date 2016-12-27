{-# OPTIONS --without-K #-}
module Relation.Binary.PropositionalEquality.Base where

open import Data.Unit.Base using () renaming (⊤ to 𝟙)
open import Data.Product using (Σ; _,_)
open import Function using (flip)
open import Relation.Binary.Bijection
  using (InjectiveRel; SurjectiveRel; BijectiveRel)
open import Relation.Binary.NP
  using (module IsEquivalence; module Refl-Trans-Reasoning)

open import Relation.Binary.PropositionalEquality.Core public
open import Relation.Binary.Core public using (_≡_; _≢_; refl)

infix 4 _≗_

_≗_ : ∀ {a b}{A : Set a}{B : A → Set b}(f g : (x : A) → B x) → Set _
f ≗ g = ∀ x → f x ≡ g x

module _ {a} {A : Set a} where
  open IsEquivalence (isEquivalence {a} {A}) public hiding (refl; sym; trans)

PathOver : ∀ {i j} {A : Set i} (B : A → Set j)
  {x y : A} (p : x ≡ y) (u : B x) (v : B y) → Set j
PathOver B refl u v = (u ≡ v)

syntax PathOver B p u v =
  u ≡ v [ B ↓ p ]

{- one day this will work -}
-- pattern idp = refl

-- Some definitions with the names from Agda-HoTT
-- this is only a temporary state of affairs...
module _ {a} {A : Set a} where

    idp : {x : A} → x ≡ x
    idp = refl

    infixr 8 _∙_ _∙'_

    _∙_ _∙'_ : {x y z : A} → (x ≡ y → y ≡ z → x ≡ z)

    refl ∙ q  = q
    q ∙' refl = q

    infix 9 !_

    !_ : {x y : A} → (x ≡ y → y ≡ x)
    !_ refl = refl

ap↓ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : A → Set k}
  (g : {a : A} → B a → C a) {x y : A} {p : x ≡ y}
  {u : B x} {v : B y}
  → (u ≡ v [ B ↓ p ] → g u ≡ g v [ C ↓ p ])
ap↓ g {p = refl} refl = refl

ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
  → (x ≡ y → f x ≡ f y)
ap f p = ap↓ {A = 𝟙} f {p = refl} p

ap₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
ap₂ f {x} {y} {u} q p = ap (λ x → f x u) q ∙ ap (f y) p

apd : ∀ {i j} {A : Set i} {B : A → Set j} (f : (a : A) → B a) {x y : A}
  → (p : x ≡ y) → f x ≡ f y [ B ↓ p ]
apd f refl = refl

coe : ∀ {i} {A B : Set i} (p : A ≡ B) → A → B
coe refl x = x

coe! : ∀ {i} {A B : Set i} (p : A ≡ B) → B → A
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

    infixr 5 _▸_
    _▸_ = tr
    -- black version of ◃ = tr!

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) {a₀ a₁ b₀ b₁ c₀ c₁}
        → a₀ ≡ a₁ → b₀ ≡ b₁ → c₀ ≡ c₁ → f a₀ b₀ c₀ ≡ f a₁ b₁ c₁
cong₃ f refl refl refl = refl

_≗₂_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f g : A → B → C) → Set _
f ≗₂ g = ∀ x y → f x y ≡ g x y

module _ {a} {A : Set a} where
  J-orig : ∀ {b} (P : (x y : A) → x ≡ y → Set b) → (∀ x → P x x refl) → ∀ {x y} (p : x ≡ y) → P x y p
  J-orig P p refl = p _

  -- This version is better suited to our identity type which has the first argument as a parameter.
  -- (due to Paulin-Mohring)
  J : ∀ {b} {x : A} (P : (y : A) → x ≡ y → Set b) → P x refl → ∀ {y} (p : x ≡ y) → P y p
  J P p refl = p

  injective : InjectiveRel A _≡_
  injective p q = p ∙ ! q

  surjective : SurjectiveRel A _≡_
  surjective p q = ! p ∙ q

  bijective : BijectiveRel A _≡_
  bijective = record { injectiveREL = injective; surjectiveREL = surjective }

  Equalizer : ∀ {b} {B : A → Set b} (f g : (x : A) → B x) → Set _
  Equalizer f g = Σ A (λ x → f x ≡ g x)
  {- In a category theory context this type would the object 'E'
     and 'fst' would be the morphism 'eq : E → A' such that
     given any object O, and morphism 'm : O → A', there exists
     a unique morphism 'u : O → E' such that 'eq ∘ u ≡ m'.
  -}

  Pullback : ∀ {b c} {B : Set b} {C : Set c} (f : A → C) (g : B → C) → Set _
  Pullback {B = B} f g = Σ A (λ x → Σ B (λ y → f x ≡ g y))

module ≡-Reasoning {a} {A : Set a} where
  open Refl-Trans-Reasoning {A = A} _≡_ refl trans
    public
    renaming (_≈⟨_⟩_ to _≡⟨_⟩_;
              _≈⟨by-definition⟩_ to _≡⟨by-definition⟩_)

module ≗-Reasoning {a b} {A : Set a} {B : A → Set b} where
  open Refl-Trans-Reasoning {A = (x : A) → B x} _≗_ (λ _ → refl) (λ p q _ → trans (p _) (q _))
    public
    renaming (_≈⟨_⟩_ to _≗⟨_⟩_;
              _≈⟨by-definition⟩_ to _≗⟨by-definition⟩_)
-- -}
