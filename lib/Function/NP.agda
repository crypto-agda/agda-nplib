{-# OPTIONS --without-K #-}
module Function.NP where

open import Type
  hiding (★)
open import Algebra
  using (module Monoid; Monoid)
open import Algebra.Structures
  using (IsSemigroup)
open import Data.Nat.Base
  using (ℕ)
open import Data.Product
  using (_,_)
open import Data.Vec.N-ary
  using (N-ary; N-ary-level)
open import Category.Monad
  using () renaming (module RawMonad to Monad; RawMonad to Monad)
open import Category.Monad.Identity
  using (IdentityMonad)
open import Category.Applicative
  renaming (module RawApplicative to Applicative;
            RawApplicative to Applicative)
open import Relation.Binary
  using (IsEquivalence; module IsEquivalence; _Preserves₂_⟶_⟶_;
         module Setoid)
open import Relation.Binary.PropositionalEquality.NP
  using (ap; ap₂; _→-setoid_; _∙_)
  renaming (isEquivalence to ≡-isEquivalence)

open import Function.Base public

id-app : ∀ {f} → Applicative {f} id
id-app = Monad.rawIApplicative IdentityMonad

_→⟨_⟩_ : ∀ {a b} (A : ★ a) (n : ℕ) (B : ★ b) → ★ (N-ary-level a b n)
A →⟨ n ⟩ B = N-ary n A B

module EndoMonoid-≈ {a ℓ} {A : ★ a}
                    {_≈_ : Endo A → Endo A → ★ ℓ}
                    (isEquivalence : IsEquivalence _≈_)
                    (∘-cong : _∘′_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_)
                   where
  private
    module ≈ = IsEquivalence isEquivalence
    isSemigroup : IsSemigroup _≈_ _∘′_
    isSemigroup = record { isEquivalence = isEquivalence; assoc = λ _ _ _ → ≈.refl; ∙-cong = ∘-cong }

  monoid : Monoid a ℓ
  monoid = record { Carrier = Endo A; _≈_ = _≈_; _∙_ = _∘′_; ε = id
                  ; isMonoid = record { isSemigroup = isSemigroup
                                      ; identity = (λ _ → ≈.refl) , (λ _ → ≈.refl) } }

  open Monoid monoid public

module EndoMonoid-≡ {a} (A : ★ a) = EndoMonoid-≈ {A = A} ≡-isEquivalence (ap₂ _∘′_)

module EndoMonoid-≗ {a} (A : ★ a) = EndoMonoid-≈ (Setoid.isEquivalence (A →-setoid A))
                                                   (λ {f} {g} {h} {i} p q x → p (h x) ∙ ap g (q x))
