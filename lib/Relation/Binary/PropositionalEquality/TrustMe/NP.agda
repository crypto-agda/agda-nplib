{-# OPTIONS --without-K #-}
module Relation.Binary.PropositionalEquality.TrustMe.NP where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe public

erase : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
erase _ = trustMe
