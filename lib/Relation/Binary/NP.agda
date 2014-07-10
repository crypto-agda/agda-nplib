{-# OPTIONS --without-K #-}
{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.NP where

open import Level
open import Relation.Binary public
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)

-- could this be moved in place of Trans is Relation.Binary.Core
Trans' : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
        REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
Trans' P Q R = ∀ {i j k} (x : P i j) (xs : Q j k) → R i k

substitutive-to-reflexive : ∀ {a ℓ ℓ'} {A : Set a} {≈ : Rel A ℓ} {≋ : Rel A ℓ'}
                            → Substitutive ≋ ℓ → Reflexive ≈ → ≋ ⇒ ≈
substitutive-to-reflexive {≈ = ≈} ≡-subst ≈-refl xᵣ = ≡-subst (≈ _) xᵣ ≈-refl

substitutive⇒≡ : ∀ {a ℓ} {A : Set a} {≋ : Rel A ℓ} → Substitutive ≋ a → ≋ ⇒ _≡_
substitutive⇒≡ subst = substitutive-to-reflexive {≈ = _≡_} subst PropEq.refl

record Equality {a ℓ} {A : Set a} (_≋_ : Rel A ℓ) : Set (suc a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≋_
    subst : Substitutive _≋_ a

  open IsEquivalence isEquivalence public

  to-reflexive : ∀ {≈} → Reflexive ≈ → _≋_ ⇒ ≈
  to-reflexive = substitutive-to-reflexive subst

  to-propositional : _≋_ ⇒ _≡_
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

  infixr 2 _≈⟨by-definition⟩_

  _≈⟨by-definition⟩_ : ∀ x {y : A} → x ≈ y → x ≈ y
  _ ≈⟨by-definition⟩ x≈y = x≈y

module Equivalence-Reasoning
         {a ℓ} {A : Set a} {_≈_ : Rel A ℓ}
         (E : IsEquivalence _≈_) where
  open IsEquivalence E
  open Refl-Trans-Reasoning _≈_ refl trans public

module Preorder-Reasoning
         {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where
  open Preorder P
  open Refl-Trans-Reasoning _∼_ refl trans public
     renaming (_≈⟨_⟩_ to _∼⟨_⟩_; _≈⟨by-definition⟩_ to _∼⟨by-definition⟩_)
  open Equivalence-Reasoning isEquivalence public renaming (_∎ to _☐)

module Setoid-Reasoning {a ℓ} (s : Setoid a ℓ) where
  open Equivalence-Reasoning (Setoid.isEquivalence s) public

module _ {a r} {A : Set a} (R : Rel A r) where
    Coreflexive : Set _
    Coreflexive = ∀ {i j} → R i j → i ≡ j

    Euclidean : Set _
    Euclidean = ∀ {i j k} → R i j → R i k → R j k

    Left-Euclidean : Set _
    Left-Euclidean = ∀ {i j k} → R j i → R k i → R j k

    Lower-Bound : A → Set _
    Lower-Bound ⊥ = ∀ {i} → R ⊥ i

    Upper-Bound : A → Set _
    Upper-Bound ⊤ = ∀ {i} → R i ⊤

module _ {a r} {A : Set a} (R : Rel A r) where
    reflexive-euclidean-is-symmetric :
      Reflexive R → Euclidean R → Symmetric R
    reflexive-euclidean-is-symmetric r e ij = e ij r

    reflexive-left-euclidean-is-symmetric :
      Reflexive R → Left-Euclidean R → Symmetric R
    reflexive-left-euclidean-is-symmetric r e ij = e r ij

    symmetric-euclidean-is-transitive :
      Symmetric R → Euclidean R → Transitive R
    symmetric-euclidean-is-transitive s e ij jk = e (s ij) jk

    symmetric-left-euclidean-is-transitive :
      Symmetric R → Left-Euclidean R → Transitive R
    symmetric-left-euclidean-is-transitive s e ij jk = e ij (s jk)

    symmetric-transitive-is-euclidean :
      Symmetric R → Transitive R → Euclidean R
    symmetric-transitive-is-euclidean s t ij ik = t (s ij) ik

    symmetric-transitive-is-left-euclidean :
      Symmetric R → Transitive R → Left-Euclidean R
    symmetric-transitive-is-left-euclidean s t ji ki = t ji (s ki)

    euclidean-is-partially-reflexive :
      Euclidean R → ∀ {i j} → R i j → R j j
    euclidean-is-partially-reflexive e ij = e ij ij

    lower-bound-euclidean-is-reflexive :
      {⊥ : A} → Lower-Bound R ⊥ → Euclidean R → Reflexive R
    lower-bound-euclidean-is-reflexive b e = e b b

    upper-bound-left-euclidean-is-reflexive :
      {⊤ : A} → Upper-Bound R ⊤ → Left-Euclidean R → Reflexive R
    upper-bound-left-euclidean-is-reflexive u e = e u u
