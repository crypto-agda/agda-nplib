{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.Permutation where

open import Level
open import Data.Product.NP
open import Data.Zero
open import Data.One
open import Data.Sum
open import Data.List
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_;_≢_)

private
  _⇔_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} (R₁ : REL A B ℓ₁) (R₂ : REL A B ℓ₂) → Set _
  R₁ ⇔ R₂ = R₁ ⇒ R₂ × R₂ ⇒ R₁

  infix 2 _⇔_

⟨_,_⟩∈_ : ∀ {ℓ a b} {A : Set a} {B : Set b} (x : A) (y : B) → REL A B ℓ → Set ℓ
⟨_,_⟩∈_ x y R = R x y

data _[_↔_] {a} {A : Set a} (R : Rel A a) (x y : A) : Rel A a where

  here₁  : ∀ {j}
             (yRj : ⟨ y , j ⟩∈ R    )
           → ----------------------
             ⟨ x , j ⟩∈ R [ x ↔ y ]

  here₂  : ∀ {j}
             (xRj : ⟨ x , j ⟩∈ R   )
           → ----------------------
             ⟨ y , j ⟩∈ R [ x ↔ y ]

  there  : ∀ {i j}
             (x≢i   : x ≢ i         )
             (y≢i   : y ≢ i         )
             (iRj   : ⟨ i , j ⟩∈ R  )
           → -----------------------
             ⟨ i , j ⟩∈ R [ x ↔ y ]

module PermComm {a} {A : Set a} {R : Rel A a} where
  ⟹ : ∀ {x y} → R [ x ↔ y ] ⇒ R [ y ↔ x ]
  ⟹ (here₁ yRj)          = here₂ yRj
  ⟹ (here₂ xRj)          = here₁ xRj
  ⟹ (there x≢i x≢j iRj)  = there x≢j x≢i iRj

  lem : ∀ {x y} → R [ x ↔ y ] ⇔ R [ y ↔ x ]
  lem = (λ {_} → ⟹) , (λ {_} → ⟹)

module PermIdem {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) {x y : A} {R : Rel A a} where
  ⇐ : ∀ {x y} → R [ x ↔ y ] [ x ↔ y ] ⇒ R
  ⇐ (here₁ (here₁ yRj))          = yRj
  ⇐ (here₁ (here₂ xRj))          = xRj
  ⇐ (here₁ (there _ y≢y _))      = 𝟘-elim (y≢y ≡.refl)
  ⇐ (here₂ (here₁ yRj))          = yRj
  ⇐ (here₂ (here₂ xRj))          = xRj
  ⇐ (here₂ (there x≢x _ _))      = 𝟘-elim (x≢x ≡.refl)
  ⇐ (there x≢x _ (here₁ _))      = 𝟘-elim (x≢x ≡.refl)
  ⇐ (there _ y≢y (here₂ _))      = 𝟘-elim (y≢y ≡.refl)
  ⇐ (there _ _ (there _ _ iRj))  = iRj

  ⟹ : R ⇒ R [ x ↔ y ] [ x ↔ y ]
  ⟹ {i} {j} R
   with x ≟ i     | y ≟ i
  ... | yes x≡i   | _       rewrite x≡i = here₁ (here₂ R)
  ... | _         | yes y≡i rewrite y≡i = here₂ (here₁ R)
  ... | no x≢i    | no y≢i              = there x≢i y≢i (there x≢i y≢i R)

  lem : R ⇔ R [ x ↔ y ] [ x ↔ y ]
  lem = (λ {_} → ⟹) , λ {_} → ⇐

Permutation : ∀ {a} → Set a → Set a
Permutation A = List (A × A)

permRel : ∀ {a} {A : Set a} → (π : Permutation A) → Rel A a → Rel A a
permRel π R = foldr (λ p r → r [ proj₁ p ↔ proj₂ p ]) R π

toRel : ∀ {a} {A : Set a} → (π : Permutation A) → Rel A a
toRel π = permRel π (λ _ _ → Lift 𝟙)

{-
  _⟨$⟩₁_ : ∀ {a} {A : Set a} → Permutation A → A → Maybe A
  []       ⟨$⟩₁ y = nothing
  (x ∷ xs) ⟨$⟩₁ y = if ⌊ x ≟A y ⌋ then ? else
-}
