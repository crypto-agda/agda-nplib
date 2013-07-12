{-# OPTIONS --without-K #-}
{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.Bijection where

open import Level
open import Function
open import Data.Sum
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_;_≢_)

InjectiveREL : ∀ {a b ℓ} (A : Set a) (B : Set b) → REL A B ℓ → Set _
InjectiveREL _ _ _∼_ = ∀ {x y z} → x ∼ z → y ∼ z → x ≡ y

InjectiveRel : ∀ {a ℓ} (A : Set a) → Rel A ℓ → Set _
InjectiveRel A = InjectiveREL A A

SurjectiveREL : ∀ {a b ℓ} (A : Set a) (B : Set b) → REL A B ℓ → Set _
SurjectiveREL A B ∼ = InjectiveREL B A (flip ∼)

SurjectiveRel : ∀ {a ℓ} (A : Set a) → Rel A ℓ → Set _
SurjectiveRel A = SurjectiveREL A A

record BijectiveREL {a b ℓ} (A : Set a) (B : Set b) (∼ : REL A B ℓ) : Set (ℓ ⊔ a ⊔ b) where
  constructor mkBijectiveREL
  field
    injectiveREL  : InjectiveREL A B ∼
    surjectiveREL : SurjectiveREL A B ∼

BijectiveRel : ∀ {a ℓ} (A : Set a) (∼ : Rel A ℓ) → Set _
BijectiveRel A = BijectiveREL A A

{-
private
  -- probably already defined somewhere
  _`on`_ : ∀ {a ℓ} {A : Set a} (f : A → A) → Rel A ℓ → Rel A ℓ
  _`on`_ f _∼_ i j = f i ∼ f j

module Pres-Bij-Props
                 {a} {A : Set a}
                 (f : A → A)
                 (f-inj : ∀ {i j} → f i ≡ f j → i ≡ j) where
  pres-bij : ∀ {ℓ} {α : Rel A ℓ} → BijectiveREL A A α → BijectiveREL A A (f `on` α)
  pres-bij {_} {α} α-bij
     = record { injectiveREL = λ {x} {y} {z} → α+-inj {x} {y} {z}
              ; surjectiveREL = λ {x} {y} {z} → α+-sur {x} {y} {z} }
     where
       open BijectiveREL α-bij renaming (injectiveREL to α-inj; surjectiveREL to α-sur)
       α+-inj : InjectiveREL A A (f `on` α)
       α+-inj fx⟨α⟩fz fy⟨α⟩fz = f-inj (α-inj fx⟨α⟩fz fy⟨α⟩fz)
       α+-sur : SurjectiveREL A A (f `on` α)
       α+-sur fx⟨α⟩fz fy⟨α⟩fz = f-inj (α-sur fx⟨α⟩fz fy⟨α⟩fz)
-}
