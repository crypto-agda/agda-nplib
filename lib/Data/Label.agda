module Data.Label where

open import Type
open import Function
open import Data.Nat using (ℕ ; suc ; zero) renaming (_≟_ to _≟ℕ_)
open import Data.List as L
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

abstract
  Label : ★
  Label = ℕ

  _≟ℓ_ : Decidable {A = Label} _≡_
  _≟ℓ_ = _≟ℕ_

LabelAssoc    : ★ → ★
LabelAssoc A  = List (Label × A)

lbls : ∀ {A : ★} → LabelAssoc A → List Label
lbls = L.map proj₁

select : ∀ {A : ★} → Label → LabelAssoc A → Maybe A
select ℓ xs with filter (⌊_⌋ ∘ _≟ℓ_ ℓ ∘ proj₁) xs
... | []           = nothing
... | (_ , x) ∷ _  = just x

update : ∀ {A : ★} → Label → A → LabelAssoc A → LabelAssoc A
update {A} ℓ a = L.map f
  where f : (Label × A) → (Label × A)
        f (ℓ' , a') with ℓ ≟ℓ ℓ'
        ... | yes  _ = (ℓ' , a)
        ... | no   _ = (ℓ' , a')

-- gs takes precedence of fs
merge : ∀ {A : ★} (fs gs : LabelAssoc A) → LabelAssoc A
merge fs []              = fs
merge fs ((ℓ , a) ∷ gs)  = merge (update ℓ a fs) gs
