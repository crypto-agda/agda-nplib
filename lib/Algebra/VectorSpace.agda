{-# OPTIONS --without-K #-}
open import Level.NP
open import Function.Extensionality
open import Algebra.Monoid
open import Algebra.Monoid.Homomorphism
open import Algebra.Group
open import Algebra.Group.Constructions
open import Algebra.Group.Homomorphism
open import Algebra.Field
open import Algebra.Ring.Homomorphism
open import Relation.Binary.PropositionalEquality.NP

module Algebra.VectorSpace {{_ : FunExt}} where

record VectorSpace {ℓf}{F : Set ℓf}(𝔽 : Field F)
                   {ℓv}(V : Set ℓv) : Set (ℓf ⊔ ℓv) where
  inductive -- NO_ETA

  module 𝔽 = Field {ℓf} {F} 𝔽

  infixr 8 _·_

  field

    V-grp : Group V

    _·_   : F → V → V

{-
    _·_ : (F × V) → V
    _·_ : F → (V → V)
    _·_ : F → Endo V
-}

    +-·-hom : GroupHomomorphism  𝔽.+-grp (Pointwise′.grp V V-grp) _·_
    *-·-hom : MonoidHomomorphism 𝔽.*-mon (∘-mon V) _·_

  module +-·-hom = GroupHomomorphism  +-·-hom
  module *-·-hom = MonoidHomomorphism *-·-hom

--    ·-hom : RingHomomorphism 𝔽.ring ?

  open 𝔽
  open Additive-Group V-grp using () renaming (_+_ to _⊕_; 0# to 0P)

  module Alternative
    (+-·-hom' : ∀ v → GroupHomomorphism 𝔽.+-grp V-grp (λ a → a · v))
    where
    module +-·-hom' {v} = GroupHomomorphism (+-·-hom' v)

    +-· : ∀ {v a b} → (a + b) · v ≡ a · v ⊕ b · v
    +-· = +-·-hom'.+-hom-*

    0-· : ∀ {v} → 0# · v ≡ 0P
    0-· = +-·-hom'.0-hom-1

  +-· : ∀ {v a b} → (a + b) · v ≡ a · v ⊕ b · v
  +-· {v} = ap (λ f → f v) +-·-hom.+-hom-*

  0-· : ∀ {v} → 0# · v ≡ 0P
  0-· {v} = ap (λ f → f v) +-·-hom.0-hom-1

  *-· : ∀ {v a b} → (a * b) · v ≡ a · (b · v)
  *-· {v} = ap (λ f → f v) *-·-hom.+-hom-*

  1-· : ∀ {v} → 1# · v ≡ v
  1-· {v} = ap (λ f → f v) *-·-hom.0-hom-1

  module Alternative'
    (hom' : ∀ a → GroupHomomorphism V-grp V-grp (λ v → a · v))
    where
    module hom' a = GroupHomomorphism (hom' a)

    ·-⊕ : ∀ {v w a} → a · (v ⊕ w) ≡ a · v ⊕ a · w
    ·-⊕ {v} {w} {a} = hom'.hom a

{-
φ(a + b) x = φ a x * φ b x

  _·_ a + b) ≡ _·_(a) ∘ _·_(b)


  {-
  _·_(a + b) ≡ _·_(a) ∘ _·_(b)
  ∀ v → _·_(a + b) v ≡ (_·_(a) ∘ _·_(b)) v
  ∀ v → (a + b) · v ≡ a · (b · v)
  -}
-- -}
-- -}
-- -}
-- -}
