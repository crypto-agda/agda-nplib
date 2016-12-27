{-# OPTIONS --without-K #-}
module Category where

open import Level
open import Type hiding (★)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;trans)
import Function.NP as F
open F using (-→-)

record RawCategory {ℓ} (_↝_ : Rel (★ ℓ) ℓ) : ★ (suc ℓ) where
  infixr 9 _∘_
  field
    id  : ∀ {A : ★ ℓ} → A ↝ A
    _∘_ : ∀ {A B C : ★ ℓ} → B ↝ C → A ↝ B → A ↝ C

record IsCategory {ℓ} {_↝_ : Rel (★ ℓ) ℓ}
                  (cat : RawCategory _↝_) : ★ (suc ℓ) where
  open RawCategory cat
  field
    id-∘ : ∀ {A B : ★ ℓ} {f : A ↝ B} → id ∘ f ≡ f
    ∘-id : ∀ {A B : ★ ℓ} {f : A ↝ B} → f ∘ id ≡ f
    ∘-assoc : ∀ {A B C D : ★ ℓ} {h : C ↝ D} {g : B ↝ C} {f : A ↝ B}
              → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
  open RawCategory cat public

record Category {ℓ} (_↝_ : Rel (★ ℓ) ℓ) : ★ (suc ℓ) where
  field
    rawCat : RawCategory _↝_
    isCat  : IsCategory rawCat
  open IsCategory isCat public

→-cat : ∀ {ℓ} → Category {ℓ} -→-
→-cat = record
  { rawCat = record { id = F.id ; _∘_ = F._∘′_ }
  ; isCat  = record { id-∘ = refl; ∘-id = refl; ∘-assoc = refl }
  }
