{-# OPTIONS --without-K #-}
open import Level.NP
open import Function.Extensionality
open import Algebra.Monoid
open import Algebra.Monoid.Homomorphism
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Algebra.Field
open import Algebra.Ring.Homomorphism
open import Relation.Binary.PropositionalEquality.NP

module Algebra.VectorSpace {{_ : FunExt}} where

record VectorSpace {ℓf}{F : Set ℓf}(𝔽 : Field F)
                   {ℓv}(V : Set ℓv) : Set (ℓf ⊔ ℓv) where

  module 𝔽 = Field {ℓf} {F} 𝔽

  field

    V-grp : Group V

    _·_   : F → V → V

{-
    _·_ : (F × V) → V
    _·_ : F → (V → V)
    _·_ : F → Endo V
-}

    ·-+ : MonoidHomomorphism 𝔽.+-mon (Pointwise′.mon V (Group.mon V-grp)) _·_
    ·-* : MonoidHomomorphism 𝔽.*-mon (∘-mon V) _·_

--    ·-hom : RingHomomorphism 𝔽.ring ?

  open 𝔽
  open Additive-Group V-grp using () renaming (_+_ to _⊕_)

  module Alternative
    (·-+ : ∀ v → GroupHomomorphism 𝔽.+-grp V-grp (λ a → a · v))
    where
    ·-+' : ∀ {v a b} → (a + b) · v ≡ a · v ⊕ b · v
    ·-+' = GroupHomomorphism.hom (·-+ _)

  ·-+' : ∀ {v a b} → (a + b) · v ≡ a · v ⊕ b · v
  ·-+' {v} = ap (λ f → f v) (MonoidHomomorphism.+-hom-* ·-+)

  ·-*' : ∀ {v a b} → (a * b) · v ≡ a · (b · v)
  ·-*' {v} = ap (λ f → f v) (MonoidHomomorphism.+-hom-* ·-*)
  {-
  _·_(a * b) ≡ _·_(a) ∘ _·_(b)
  ∀ v → _·_(a * b) v ≡ (_·_(a) ∘ _·_(b)) v
  ∀ v → (a * b) · v ≡ a · (b · v)
  -}

  ·-1 : ∀ {v} → 1# · v ≡ v
  ·-1 {v} = ap (λ f → f v) (MonoidHomomorphism.0-hom-1 ·-*)
  {-
  _·_ 1# ≡ id
  ∀ v → _·_ 1# v ≡ id v
  ∀ v → 1# · v ≡ v
  -}

--  ·-⊕ : ∀ {v w a} → a · (v ⊕ w) ≡ a · v ⊕ a · w
--  ·-⊕ {v} {w} {a} = {!!}
  {-
  _·_(a + b) ≡ _·_(a) ∘ _·_(b)
  ∀ v → _·_(a + b) v ≡ (_·_(a) ∘ _·_(b)) v
  ∀ v → (a + b) · v ≡ a · (b · v)
  -}
-- -}
-- -}
-- -}
-- -}
