open import Type
import Data.Nat.NP as ℕ
open ℕ using (ℕ; zero; suc; module ℕ≤)
open import Data.Bool
open import Data.Zero using (𝟘; 𝟘-elim)
open import Data.Sum renaming (map to ⊎-map)
open import Function
open import Relation.Binary
open import Algebra.FunctionProperties
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

module Relation.Binary.ToNat {a} {A : Set a} (f : A → ℕ) (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y) where

_<=_ : A → A → Bool
_<=_ = ℕ._<=_ on f 

_≤_ : A → A → ★
x ≤ y = T (x <= y)

_⊓_ : A → A → A
x ⊓ y = if x <= y then x else y

_⊔_ : A → A → A
x ⊔ y = if x <= y then y else x

isPreorder : IsPreorder _≡_ _≤_
isPreorder = record { isEquivalence = ≡.isEquivalence
                    ; reflexive = reflexive
                    ; trans = λ {x} {y} {z} → trans {x} {y} {z} }
  where open ℕ.<= using (sound; complete)
        reflexive : ∀ {i j} → i ≡ j → i ≤ j
        reflexive {i} ≡.refl = complete (ℕ≤.refl {f i})
        trans : Transitive _≤_
        trans {x} {y} {z} p q = complete (ℕ≤.trans (sound (f x) (f y) p) (sound (f y) (f z) q))

isPartialOrder : IsPartialOrder _≡_ _≤_
isPartialOrder = record { isPreorder = isPreorder; antisym = antisym }
  where open ℕ.<= using (sound)
        antisym : Antisymmetric _≡_ _≤_
        antisym {x} {y} p q = f-inj (ℕ≤.antisym (sound (f x) (f y) p) (sound (f y) (f x) q))

isTotalOrder : IsTotalOrder _≡_ _≤_
isTotalOrder = record { isPartialOrder = isPartialOrder; total = λ x y → ⊎-map complete complete (ℕ≤.total (f x) (f y)) }
  where open ℕ.<= using (complete)

open IsTotalOrder isTotalOrder

⊔-spec : ∀ {x y} → x ≤ y → x ⊔ y ≡ y
⊔-spec {x} {y} p with x <= y
⊔-spec _    | true = ≡.refl
⊔-spec ()   | false

⊓-spec : ∀ {x y} → x ≤ y → x ⊓ y ≡ x
⊓-spec {x} {y} p with x <= y
⊓-spec _    | true = ≡.refl
⊓-spec ()   | false

⊓-comm : Commutative _≡_ _⊓_
⊓-comm x y with x <= y | y <= x | antisym {x} {y} | total x y
... | true | true   | p | _ = p _ _
... | true | false  | _ | _ = ≡.refl
... | false | true  | _ | _ = ≡.refl
... | false | false | _ | p = 𝟘-elim ([ id , id ] p)

⊔-comm : Commutative _≡_ _⊔_
⊔-comm x y with x <= y | y <= x | antisym {y} {x} | total x y
... | true | true   | p | _ = p _ _
... | true | false  | _ | _ = ≡.refl
... | false | true  | _ | _ = ≡.refl
... | false | false | _ | p = 𝟘-elim ([ id , id ] p)

⊓-≤ : ∀ x y → (x ⊓ y) ≤ y
⊓-≤ x y with total x y
⊓-≤ x y | inj₁ p rewrite ⊓-spec p = p
⊓-≤ x y | inj₂ p rewrite ⊓-comm x y | ⊓-spec p = refl

≤-⊔ : ∀ x y → x ≤ (y ⊔ x)
≤-⊔ x y with total x y
≤-⊔ x y | inj₁ p rewrite ⊔-comm y x | ⊔-spec p = p
≤-⊔ x y | inj₂ p rewrite ⊔-spec p = refl

≤-<_,_> : ∀ {x y z} → x ≤ y → x ≤ z → x ≤ (y ⊓ z)
≤-<_,_> {x} {y} {z} x≤y y≤z with total y z
... | inj₁ p rewrite ⊓-spec p = x≤y
... | inj₂ p rewrite ⊓-comm y z | ⊓-spec p = y≤z

≤-[_,_] : ∀ {x y z} → x ≤ z → y ≤ z → (x ⊔ y) ≤ z
≤-[_,_] {x} {y} {z} x≤z y≤z with total x y
... | inj₁ p rewrite ⊔-spec p = y≤z
... | inj₂ p rewrite ⊔-comm x y | ⊔-spec p = x≤z

≤-⊓₀ : ∀ {x y z} → x ≤ (y ⊓ z) → x ≤ y
≤-⊓₀ {x} {y} {z} with total y z
... | inj₁ p rewrite ⊓-spec p = id
... | inj₂ p rewrite ⊓-comm y z | ⊓-spec p = flip trans p

≤-⊓₁ : ∀ {x y z} → x ≤ (y ⊓ z) → x ≤ z
≤-⊓₁ {x} {y} {z} with total y z
... | inj₁ p rewrite ⊓-spec p = flip trans p
... | inj₂ p rewrite ⊓-comm y z | ⊓-spec p = id

≤-⊔₀ : ∀ {x y z} → (x ⊔ y) ≤ z → x ≤ z
≤-⊔₀ {x} {y} {z} with total x y
... | inj₁ p rewrite ⊔-spec p = trans p
... | inj₂ p rewrite ⊔-comm x y | ⊔-spec p = id

≤-⊔₁ : ∀ {x y z} → (x ⊔ y) ≤ z → y ≤ z
≤-⊔₁ {x} {y} {z} with total x y
... | inj₁ p rewrite ⊔-spec p = id
... | inj₂ p rewrite ⊔-comm x y | ⊔-spec p = trans p
