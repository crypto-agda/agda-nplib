module Algebra.NP where

open import Type hiding (★)
open import Algebra public
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Function
open import Data.Product
open import Relation.Binary

module Flip where
    module Structures {c} {C : ★ c} {ℓ} (_≈_ : C → C → ★ ℓ) (_∙_ : Op₂ C) where
        flipIsSemigroup : IsSemigroup _≈_ _∙_ → IsSemigroup _≈_ (flip _∙_)
        flipIsSemigroup isSg = record { isEquivalence = isEquivalence
                                      ; assoc = λ x y z → sym (assoc z y x)
                                      ; ∙-cong = λ p q → sym (∙-cong (sym q) (sym p)) }
            where open IsSemigroup isSg

        flipIsMonoid : ∀ {ε} → IsMonoid _≈_ _∙_ ε → IsMonoid _≈_ (flip _∙_) ε
        flipIsMonoid isMon = record { isSemigroup = flipIsSemigroup isSemigroup
                                    ; identity    = swap identity }
            where open IsMonoid isMon

        flipIsCommutativeMonoid : ∀ {ε} → IsCommutativeMonoid _≈_ _∙_ ε
                                        → IsCommutativeMonoid _≈_ (flip _∙_) ε
        flipIsCommutativeMonoid isCMon
          = record { isSemigroup = flipIsSemigroup isSemigroup
                   ; identityˡ = proj₂ identity; comm = flip comm }
            where open IsCommutativeMonoid isCMon

        flipIsGroup : ∀ {ε} {_⁻¹} → IsGroup _≈_ _∙_ ε _⁻¹ → IsGroup _≈_ (flip _∙_) ε _⁻¹
        flipIsGroup isGr = record { isMonoid = flipIsMonoid isMonoid
                                  ; inverse = swap inverse
                                  ; ⁻¹-cong = ⁻¹-cong }
            where open IsGroup isGr

        flipIsAbelianGroup : ∀ {ε} {_⁻¹} → IsAbelianGroup _≈_ _∙_ ε _⁻¹
                                         → IsAbelianGroup _≈_ (flip _∙_) ε _⁻¹
        flipIsAbelianGroup isAGr = record { isGroup = flipIsGroup isGroup
                                          ; comm    = flip comm }
            where open IsAbelianGroup isAGr

    flipSemigroup : ∀ {c ℓ} → Semigroup c ℓ → Semigroup c ℓ
    flipSemigroup sg = record { isSemigroup = flipIsSemigroup isSemigroup }
      where open Semigroup sg
            open Structures _≈_ _∙_

    flipMonoid : ∀ {c ℓ} → Monoid c ℓ → Monoid c ℓ
    flipMonoid m = record { isMonoid = flipIsMonoid isMonoid }
      where open Monoid m
            open Structures _≈_ _∙_

    flipCommutativeMonoid : ∀ {c ℓ} → CommutativeMonoid c ℓ → CommutativeMonoid c ℓ
    flipCommutativeMonoid cm
      = record { isCommutativeMonoid = flipIsCommutativeMonoid isCommutativeMonoid }
      where open CommutativeMonoid cm
            open Structures _≈_ _∙_

    flipGroup : ∀ {c ℓ} → Group c ℓ → Group c ℓ
    flipGroup gr = record { isGroup = flipIsGroup isGroup }
      where open Group gr
            open Structures _≈_ _∙_

    flipAbelianGroup : ∀ {c ℓ} → AbelianGroup c ℓ → AbelianGroup c ℓ
    flipAbelianGroup agr = record { isAbelianGroup = flipIsAbelianGroup isAbelianGroup }
      where open AbelianGroup agr
            open Structures _≈_ _∙_
