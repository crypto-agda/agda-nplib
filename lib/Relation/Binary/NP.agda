{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.NP where

open import Level
open import Relation.Binary public
import Relation.Binary.PropositionalEquality as PropEq

-- could this be moved in place of Trans is Relation.Binary.Core
Trans' : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
        REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
Trans' P Q R = ∀ {i j k} (x : P i j) (xs : Q j k) → R i k

substitutive-to-reflexive : ∀ {a ℓ ℓ'} {A : Set a} {≈ : Rel A ℓ} {≡ : Rel A ℓ'}
                            → Substitutive ≡ ℓ → Reflexive ≈ → ≡ ⇒ ≈
substitutive-to-reflexive {≈ = ≈} ≡-subst ≈-refl xᵣ = ≡-subst (≈ _) xᵣ ≈-refl

substitutive⇒≡ : ∀ {a ℓ} {A : Set a} {≡ : Rel A ℓ} → Substitutive ≡ a → ≡ ⇒ PropEq._≡_
substitutive⇒≡ subst = substitutive-to-reflexive {≈ = PropEq._≡_} subst PropEq.refl

record Equality {a ℓ} {A : Set a} (_≡_ : Rel A ℓ) : Set (suc a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≡_
    subst : Substitutive _≡_ a

  open IsEquivalence isEquivalence public

  to-reflexive : ∀ {≈} → Reflexive ≈ → _≡_ ⇒ ≈
  to-reflexive = substitutive-to-reflexive subst

  to-propositional : _≡_ ⇒ PropEq._≡_
  to-propositional = substitutive⇒≡ subst

-- Equational reasoning combinators.

module Trans-Reasoning {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (trans : Transitive _≈_) where

  infix  2 finally
  infixr 2 _≈⟨_⟩_

  _≈⟨_⟩_ : ∀ x {y z : A} → x ≈ y → y ≈ z → x ≈ z
  _ ≈⟨ x≈y ⟩ y≈z = trans x≈y y≈z

  -- When there is no reflexivty available this
  -- combinator can be used to end the reasoning.
  finally : ∀ (x y : A) → x ≈ y → x ≈ y
  finally _ _ x≈y = x≈y

  syntax finally x y x≈y = x ≈⟨ x≈y ⟩∎ y ∎

module Refl-Trans-Reasoning
         {a ℓ} {A : Set a} (_≈_ : Rel A ℓ)
         (refl : Reflexive _≈_)
         (trans : Transitive _≈_) where

  open Trans-Reasoning _≈_ trans public hiding (finally)
  infix  2 _∎

  _∎ : ∀ x → x ≈ x
  _ ∎ = refl

module Equivalence-Reasoning
         {a ℓ} {A : Set a} {_≈_ : Rel A ℓ}
         (E : IsEquivalence _≈_) where
  open IsEquivalence E
  open Refl-Trans-Reasoning _≈_ refl trans public

module Preorder-Reasoning
         {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where
  open Preorder P
  open Refl-Trans-Reasoning _∼_ refl trans public renaming (_≈⟨_⟩_ to _∼⟨_⟩_)
  open Equivalence-Reasoning isEquivalence public renaming (_∎ to _☐)

module Setoid-Reasoning {a ℓ} (s : Setoid a ℓ) where
  open Equivalence-Reasoning (Setoid.isEquivalence s) public
