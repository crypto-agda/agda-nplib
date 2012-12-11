module Category where

open import Level
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;trans)
import Function.NP as F
open F using (-→-)

record RawCategory {ℓ} (_↝_ : Rel (Set ℓ) ℓ) : Set (suc ℓ) where
  field
    id  : ∀ {A : Set ℓ} → A ↝ A
    _∘_ : ∀ {A B C : Set ℓ} → B ↝ C → A ↝ B → A ↝ C

record IsCategory {ℓ} {_↝_ : Rel (Set ℓ) ℓ}
                  (cat : RawCategory _↝_) : Set (suc ℓ) where
  open RawCategory cat
  field
    id-∘ : ∀ {A B : Set ℓ} {f : A ↝ B} → id ∘ f ≡ f
    ∘-id : ∀ {A B : Set ℓ} {f : A ↝ B} → f ∘ id ≡ f
    ∘-assoc : ∀ {A B C D : Set ℓ} {h : C ↝ D} {g : B ↝ C} {f : A ↝ B}
              → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
  open RawCategory cat public

record Category {ℓ} (_↝_ : Rel (Set ℓ) ℓ) : Set (suc ℓ) where
  field
    rawCat : RawCategory _↝_
    isCat  : IsCategory rawCat
  open IsCategory isCat public

→-cat : ∀ {ℓ} → Category {ℓ} -→-
→-cat = record
  { rawCat = record { id = F.id ; _∘_ = F._∘′_ }
  ; isCat  = record { id-∘ = refl; ∘-id = refl; ∘-assoc = refl }
  }
