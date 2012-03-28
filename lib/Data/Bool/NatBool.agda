{-# OPTIONS --universe-polymorphism #-}
-- This is an example of the use of logical relations
module Data.Bool.NatBool where

open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.Logical
open import Level
import Data.Bool

record BOOL : Set₁ where
  constructor mkBOOL
  field
    B           : Set
    true false  : B
    _∨_         : B → B → B

module Implem where
  ℕBool : Set
  ℕBool = ℕ

  false : ℕBool
  false = 0

  true : ℕBool
  true = 1

  _∨_ : ℕBool → ℕBool → ℕBool
  m ∨ n = m + n

  -- this function breaks the abstraction/model
  is4? : ℕBool → ℕBool
  is4? 4 = true
  is4? _  = false

  bool : BOOL
  bool = mkBOOL ℕBool true false _∨_

module Model where
  open Implem

  data ⟦ℕBool⟧ : (x y : ℕBool) → Set where
    ⟦false⟧ : ⟦ℕBool⟧ 0 0
    ⟦true⟧  : ∀ {m n} → ⟦ℕBool⟧ (suc m) (suc n)

  _⟦∨⟧_ : (⟦ℕBool⟧ ⟦→⟧ ⟦ℕBool⟧ ⟦→⟧ ⟦ℕBool⟧) _∨_ _∨_
  ⟦false⟧  ⟦∨⟧  x = x
  ⟦true⟧   ⟦∨⟧  _ = ⟦true⟧

  ¬⟦is4?⟧ : ¬((⟦ℕBool⟧ ⟦→⟧ ⟦ℕBool⟧) is4? is4?)
  ¬⟦is4?⟧ ⟦is4?⟧ with ⟦is4?⟧ {4} {3} ⟦true⟧
  ...               | ()

reference : BOOL
reference = mkBOOL Ref.Bool Ref.true Ref.false Ref._∨_
  where module Ref = Data.Bool

record BOOL-Sound (bool : BOOL) : Set₁ where
  constructor mk⟦BOOL⟧
  open BOOL bool
  field
    ⟦B⟧      : ⟦Set₀⟧ B B
    ⟦true⟧   : ⟦B⟧ true true
    ⟦false⟧  : ⟦B⟧ false false
    _⟦∨⟧_    : (⟦B⟧ ⟦→⟧ ⟦B⟧ ⟦→⟧ ⟦B⟧) _∨_ _∨_

reference-sound : BOOL-Sound reference
reference-sound = mk⟦BOOL⟧ _≡_ refl refl _⟦∨⟧_
  where module Ref = Data.Bool
        open import Relation.Binary.PropositionalEquality
        _⟦∨⟧_ : (_≡_ ⟦→⟧ _≡_ ⟦→⟧ _≡_) Ref._∨_ Ref._∨_
        _⟦∨⟧_ refl refl = refl

BOOL-sound : BOOL-Sound Implem.bool
BOOL-sound = mk⟦BOOL⟧ ⟦ℕBool⟧ ⟦true⟧ ⟦false⟧ _⟦∨⟧_
  where open Implem
        open Model

record ⟦BOOL⟧ (x y : BOOL) : Set₁ where
  constructor mk⟦BOOL⟧
  module X = BOOL x
  module Y = BOOL y
  field
    ⟦B⟧      : ⟦Set₀⟧ X.B Y.B
    ⟦true⟧   : ⟦B⟧ X.true Y.true
    ⟦false⟧  : ⟦B⟧ X.false Y.false
    _⟦∨⟧_    : (⟦B⟧ ⟦→⟧ ⟦B⟧ ⟦→⟧ ⟦B⟧) X._∨_ Y._∨_

⟦Implem-bool⟧ : ⟦BOOL⟧ Implem.bool Implem.bool
⟦Implem-bool⟧ = mk⟦BOOL⟧ ⟦ℕBool⟧ ⟦true⟧ ⟦false⟧ _⟦∨⟧_
  where open Implem
        open Model

⟦reference⟧ : ⟦BOOL⟧ reference reference
⟦reference⟧ = mk⟦BOOL⟧ _≡_ refl refl _⟦∨⟧_
  where module Ref = Data.Bool
        open import Relation.Binary.PropositionalEquality
        _⟦∨⟧_ : (_≡_ ⟦→⟧ _≡_ ⟦→⟧ _≡_) Ref._∨_ Ref._∨_
        _⟦∨⟧_ refl refl = refl

⟦bool-ref⟧ : ⟦BOOL⟧ Implem.bool reference
⟦bool-ref⟧ = mk⟦BOOL⟧ ⟦B⟧ ⟦true⟧ ⟦false⟧ _⟦∨⟧_
  where
    open Implem    renaming (_∨_ to _∨₁_)
    open Data.Bool renaming (false to false₂; true to true₂; _∨_ to _∨₂_)

    data ⟦B⟧ : ℕBool → Bool → Set where
      ⟦false⟧ : ⟦B⟧ 0 false₂
      ⟦true⟧  : ∀ {m} → ⟦B⟧ (suc m) true₂

    _⟦∨⟧_ : (⟦B⟧ ⟦→⟧ ⟦B⟧ ⟦→⟧ ⟦B⟧) _∨₁_ _∨₂_
    ⟦false⟧  ⟦∨⟧  x = x
    ⟦true⟧   ⟦∨⟧  _ = ⟦true⟧

Client : (A : BOOL → Set) → Set₁
Client A = (bool : BOOL) → A bool

{-
open import Data.Unit
open import Data.Empty

⟦ℕBool⟧ : (x y : ℕBool) → Set
⟦ℕBool⟧ 0        0        = ⊤
⟦ℕBool⟧ (suc _)  (suc _)  = ⊤
⟦ℕBool⟧ _        _        = ⊥

_⟦∨⟧_ : (⟦ℕBool⟧ ⟦→⟧ ⟦ℕBool⟧ ⟦→⟧ ⟦ℕBool⟧) _∨_ _∨_
_⟦∨⟧_ _ {zero} {suc _} ()
_⟦∨⟧_ _ {suc _} {zero} ()
_⟦∨⟧_ {zero} {suc _} () _
_⟦∨⟧_ {suc _} {zero} () _
_⟦∨⟧_ {zero} {zero} _ {zero} {zero} _ = _
_⟦∨⟧_ {zero} {zero} _ {suc _} {suc _} _ = _
_⟦∨⟧_ {suc _} {suc _} _ {zero} {zero} _ = _
_⟦∨⟧_ {suc _} {suc _} _ {suc _} {suc _} _ = _

¬⟦is4?⟧ : ¬((⟦ℕBool⟧ ⟦→⟧ ⟦ℕBool⟧) is4? is4?)
¬⟦is4?⟧ ⟦is4?⟧ = ⟦is4?⟧ {4} {2} _
-}
{-

import Data.Bool as B
open B using (Bool)

toBool : ℕBool → Bool
toBool 0 = B.false
toBool _ = B.true

not : ℕBool → ℕBool
not 0 = true
not _ = false

even : ℕBool → ℕBool
even zero     = true
even (suc n)  = not (even n)

¬⟦even⟧ : ¬((⟦ℕBool⟧ ⟦→⟧ ⟦ℕBool⟧) even even)
¬⟦even⟧ ⟦even⟧ with ⟦even⟧ {1} {2} ⟦true⟧
... | ()

open import Data.Nat.Logical

toℕ : ℕBool → ℕ
toℕ n = n

¬⟦toℕ⟧ : ¬((⟦ℕBool⟧ ⟦→⟧ ⟦ℕ⟧) toℕ toℕ)
¬⟦toℕ⟧ ⟦toℕ⟧ with ⟦toℕ⟧ {1} {2} ⟦true⟧
... | suc ()
-}
