{-# OPTIONS --without-K #-}
{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.On.NP where

import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_;_≢_)
open import Function
open import Relation.Binary.NP
open import Relation.Binary.Bijection
open import Relation.Binary.On public

private
  module Dummy {a b} {A : Set a} {B : Set b} (f : B → A) where

    module Inj (f-inj : ∀ {i j} → f i ≡ f j → i ≡ j) where
      injective : ∀ {ℓ} {∼ : Rel A ℓ} → InjectiveRel A ∼ → InjectiveRel B (∼ on f)
      injective ∼-inj fx∼fz fy∼fz = f-inj (∼-inj fx∼fz fy∼fz)

      surjective : ∀ {ℓ} {∼ : Rel A ℓ} → SurjectiveRel A ∼ → SurjectiveRel B (∼ on f)
      surjective ∼-inj fx∼fz fy∼fz = f-inj (∼-inj fx∼fz fy∼fz)

      bijective : ∀ {ℓ} {∼ : Rel A ℓ} → BijectiveRel A ∼ → BijectiveRel B (∼ on f)
      bijective ∼-bij
       = record { injectiveREL = injective (λ {x} {y} {z} → ∼-inj {x} {y} {z})
                ; surjectiveREL = surjective (λ {x} {y} {z} → ∼-sur {x} {y} {z}) }
        where open BijectiveREL ∼-bij renaming (injectiveREL to ∼-inj; surjectiveREL to ∼-sur)

    open Inj public

{-
  module Hom {a} {A B : Set a} (f : B → A) where
    substitutive : ∀ ℓ' {ℓ} {≈ : Rel A ℓ} → Substitutive ≈ ℓ' → Substitutive (≈ on f) ℓ'
    substitutive ℓ' subst P xᵣ Px = subst {!P ∘ f!} xᵣ {!!}
-}

open Dummy public

--equality : ∀ {a} {A B : Set a} {f : A → B} {≡ : Rel B a} (≡-eq : Equality ≡) → Equality (≡ on f)
--equality ≡-eq = record { isEquivalence = {!Equality.isEquivalence ≡-eq!}; subst = {!Equality.subst ≡-eq!} }
