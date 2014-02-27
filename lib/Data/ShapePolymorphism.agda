{-# OPTIONS --without-K #-}
open import Type
open import Function.NP
open import Level.NP

module Data.ShapePolymorphism where

data ☐ {a}(A : ★_ a) : ★_ a where
  [_] : ..(x : A) → ☐ A

un☐ : ∀ {a b}{A : ★_ a}{B : ☐ A → ★_ b} → (..(x : A) → B [ x ]) → Π (☐ A) B
un☐ f [ x ] = f x

Π☐ : ∀ {a b}(A : ★_ a) → (B : ☐ A → ★_ b) → ★_ (a ⊔ b)
Π☐ A B = (x : ☐ A) → B x

_>>☐_ : ∀ {a b}{A : ★_ a}{B : ☐ A → ★_ b} (x : ☐ A) → (..(x : A) → B [ x ]) → B x
[ x ] >>☐ f = f x

-- This is not a proper map since the function takes a ..A.
map☐ : ∀ {a b}{A : ★_ a}{B : ★_ b} → (..(x : A) → B) → ☐ A → ☐ B
map☐ f [ x ] = [ f x ]

-- This does not work since a ☐ has to be relevant when eliminated.
-- join☐ : ∀ {a}{A : ★_ a} → ☐ (☐ A) → ☐ A

{- This is not a proper bind either.
_>>=☐_ : ∀ {a b}{A : ★_ a}{B : ★_ b} (x : ☐ A) → (..(x : A) → ☐ B) → ☐ B
_>>=☐_ = _>>☐_
-}

data _≡☐_ {a} {A : ★_ a} (x : A) : ..(y : A) → ★_ a where
  refl : x ≡☐ x

record S⟨_⟩ {a} {A : ★_ a} ..(x : A) : ★_ a where
  constructor S[_∥_]
  field
    unS : A
    isS : unS ≡☐ x
open S⟨_⟩ public

pattern S[_] x = S[ x ∥ refl ]
{-
S[_] : ∀ {a}{A : ★_ a} (x : A) → S⟨ x ⟩
S[ x ] = S[ x ∥ refl ]
-}
