{-# OPTIONS --without-K #-}
open import Data.Two hiding (_≟_; decSetoid)
open import Type
open import Relation.Binary
open import Relation.Nullary
open import Function
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

module Data.Two.Equality where

_≈_ : (x y : 𝟚) → ★₀
x ≈ y = ✓ (x == y)

refl : Reflexive _≈_
refl {0₂} = _
refl {1₂} = _

subst : ∀ {ℓ} → Substitutive _≈_ ℓ
subst _ {0₂} {0₂} _ = id
subst _ {1₂} {1₂} _ = id
subst _ {0₂} {1₂} ()
subst _ {1₂} {0₂} ()

sym : Symmetric _≈_
sym {x} {y} eq = subst (λ y → y ≈ x) {x} {y} eq (refl {x})

trans : Transitive _≈_
trans {x} {y} {z} x≈y y≈z = subst (_≈_ x) {y} {z} y≈z x≈y

_≟_ : Decidable _≈_
0₂ ≟ 0₂ = yes _
1₂ ≟ 1₂ = yes _
0₂ ≟ 1₂ = no (λ())
1₂ ≟ 0₂ = no (λ())

isEquivalence : IsEquivalence _≈_
isEquivalence = record { refl  = λ {x} → refl {x}
                       ; sym   = λ {x} {y} → sym {x} {y}
                       ; trans = λ {x} {y} {z} → trans {x} {y} {z} }

isDecEquivalence : IsDecEquivalence _≈_
isDecEquivalence = record { isEquivalence = isEquivalence; _≟_ = _≟_ }

setoid : Setoid _ _
setoid = record { Carrier = 𝟚; _≈_ = _≈_ ; isEquivalence = isEquivalence }

decSetoid : DecSetoid _ _
decSetoid = record { Carrier = 𝟚; _≈_ = _≈_; isDecEquivalence = isDecEquivalence }

neg-xor : ∀ b₀ b₁ → b₀ == b₁ ≡ not (b₀ xor b₁)
neg-xor 0₂ b = ≡.refl
neg-xor 1₂ b = ≡.sym (not-involutive b)

comm : ∀ b₀ b₁ → b₀ == b₁ ≡ b₁ == b₀
comm 0₂ 0₂ = ≡.refl
comm 0₂ 1₂ = ≡.refl
comm 1₂ 0₂ = ≡.refl
comm 1₂ 1₂ = ≡.refl
