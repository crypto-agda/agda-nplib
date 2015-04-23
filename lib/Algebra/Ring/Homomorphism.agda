{-# OPTIONS --without-K #-}
module Algebra.Ring.Homomorphism where

open import Type using (Type_)
open import Level.NP using (_⊔_)
open import Algebra.Ring
open import Algebra.Monoid.Homomorphism
open import Algebra.Group.Homomorphism

record RingHomomorphism {a}{A : Type a}{b}{B : Type b}
                        (𝔸 : Ring A)(𝔹 : Ring B)
                        (f : A → B) : Type (a ⊔ b) where
  constructor _,_

  module 𝔸 = Ring 𝔸
  module 𝔹 = Ring 𝔹

  field
    +-hom : GroupHomomorphism  𝔸.+-grp 𝔹.+-grp f
    *-hom : MonoidHomomorphism 𝔸.*-mon 𝔹.*-mon f

  module +-hom = GroupHomomorphism  +-hom
  module *-hom = MonoidHomomorphism *-hom

-- -}
-- -}
-- -}
-- -}
