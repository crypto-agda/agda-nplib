module Data.Fin.Abs (W : Set) (ø : W) (_^¹ _⁺¹ : W → W) {-; z≤n; s≤s)-} where

open import Data.Nat as Nat
  using (ℕ; zero; suc)
  renaming ( _+_ to _N+_; _∸_ to _N∸_
           ; _≤_ to _N≤_; _<_ to _N<_; _≤?_ to _N≤?_)

open import Function
open import Level hiding (lift)
open import Relation.Nullary.Decidable
open import Relation.Binary

------------------------------------------------------------------------
-- Types

-- Fin (ø ^ n) is a type with n elements.

data Fin : W → Set where
  zero : {n : W} → Fin (n ^¹)
  suc  : {n : W} (i : Fin n) → Fin (n ⁺¹)

-- A conversion: toℕ "n" = n.

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

toW : ∀ {n} → Fin n → W
toW zero    = ø
toW (suc i) = toW i ^¹

_^_ : W → ℕ → W
w ^ zero  = w
w ^ suc n = (w ^ n)^¹

_+w_ : W → ℕ → W
w +w zero  = w
w +w suc n = (w +w n)⁺¹

-- A Fin-indexed variant of Fin.

Fin′ : ∀ {n} → Fin n → Set
Fin′ i = Fin (toW i)

------------------------------------------------------------------------
-- Conversions

-- toℕ is defined above.

-- makes no sense in Abs
fromℕ : (n : ℕ) → Fin (ø ^ suc n)
fromℕ zero    = zero
fromℕ (suc n) = {!suc (fromℕ n)!}

-- fromℕ≤ {m} _ = "m".

fromℕ≤ : ∀ {m n} → m N< n → Fin (ø ^ n)
fromℕ≤ (Nat.s≤s Nat.z≤n)       = zero
fromℕ≤ (Nat.s≤s (Nat.s≤s m≤n)) = {!suc (fromℕ≤ (Nat.s≤s m≤n))!}

-- # m = "m".

#_ : ∀ m {n} {m<n : True (suc m N≤? n)} → Fin (ø ^ n)
#_ _ {m<n = m<n} = fromℕ≤ (toWitness m<n)

-- raise m "n" = "m + n".

{-
raise : ∀ {m} n → Fin m → Fin (m +w n)
raise zero    i = i
raise (suc n) i = suc (raise n i)
-}

-- TODO: conversion back and from Fin (ø ^ n) and Data.Fin.Fin n

-- inject⋆ m "n" = "n".

{-
-- makes no sense:
-- inject : ∀ {n} {i : Fin n} → Fin′ i → Fin n
inject : ∀ {n} {i : Fin (ø ^ n)} → Fin′ i → Fin (ø ^ n)
inject {n = suc _} {i = zero}  ()
inject {n = zero}  ()
inject {i = suc i} zero    = zero
inject {i = suc i} (suc j) = suc (inject j)

inject! : ∀ {n} {i : Fin (suc n)} → Fin′ i → Fin n
inject! {n = zero}  {i = suc ()} _
inject!             {i = zero}   ()
inject! {n = suc _} {i = suc _}  zero    = zero
inject! {n = suc _} {i = suc _}  (suc j) = suc (inject! j)

inject+ : ∀ {m} n → Fin m → Fin (m N+ n)
inject+ n zero    = zero
inject+ n (suc i) = suc (inject+ n i)
-}

inject₁ : ∀ {m} → Fin m → Fin (m ^¹)
inject₁ zero    = zero
inject₁ (suc i) = {!suc (inject₁ i)!}

{-
inject≤ : ∀ {m n} → Fin m → m N≤ n → Fin n
inject≤ zero    (Nat.s≤s le) = zero
inject≤ (suc i) (Nat.s≤s le) = suc (inject≤ i le)
-}

------------------------------------------------------------------------
-- Operations

-- Fold.

fold : ∀ (T : W → Set) {m} →
       (∀ {n} → T n → T (n ⁺¹)) →
       (∀ {n} → T (n ^¹)) →
       Fin m → T m
fold T f x zero    = x
fold T f x (suc i) = f (fold T f x i)

-- Lifts functions.

{- TODO
lift : ∀ {m n} k → (Fin m → Fin n) → Fin (m +w k) → Fin (n +w k)
lift zero    f i       = f i
lift (suc k) f zero    = zero
lift (suc k) f (suc i) = suc (lift k f i)
-}

-- "m" + "n" = "m + n".

infixl 6 _+_

_+_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (n +w toℕ i)
zero  + j = j
suc i + j = suc (i + j)

-- "m" - "n" = "m ∸ n".

{-
infixl 6 _-_

_-_ : ∀ {m} (i : Fin m) (j : Fin′ (suc i)) → Fin (m N∸ toℕ j)
i     - zero   = i
zero  - suc ()
suc i - suc j  = i - j

-- m ℕ- "n" = "m ∸ n".

infixl 6 _ℕ-_

_ℕ-_ : (n : ℕ) (j : Fin (suc n)) → Fin (suc n N∸ toℕ j)
n     ℕ- zero   = fromℕ n
zero  ℕ- suc ()
suc n ℕ- suc i  = n ℕ- i

-- m ℕ-ℕ "n" = m ∸ n.

infixl 6 _ℕ-ℕ_

_ℕ-ℕ_ : (n : ℕ) → Fin (suc n) → ℕ
n     ℕ-ℕ zero   = n
zero  ℕ-ℕ suc ()
suc n ℕ-ℕ suc i  = n ℕ-ℕ i

-- pred "n" = "pred n".

pred : ∀ {n} → Fin n → Fin n
pred zero    = zero
pred (suc i) = inject₁ i

------------------------------------------------------------------------
-- Order relations

infix 4 _≤_ _<_

_≤_ : ∀ {n} → Rel (Fin n) zero
_≤_ = _N≤_ on toℕ

_<_ : ∀ {n} → Rel (Fin n) zero
_<_ = _N<_ on toℕ

data _≺_ : ℕ → ℕ → Set where
  _≻toℕ_ : ∀ n (i : Fin n) → toℕ i ≺ n

-- An ordering view.

data Ordering {n : W} : Fin n → Fin n → Set where
  less    : ∀ greatest (least : Fin′ greatest) →
            Ordering ({!inject!} least) greatest
  equal   : ∀ i → Ordering i i
  greater : ∀ greatest (least : Fin′ greatest) →
            Ordering greatest ({!inject!} least)

compare : ∀ {n} (i j : Fin n) → Ordering i j
compare zero    zero    = equal   zero
compare zero    (suc j) = less    (suc j) zero
compare (suc i) zero    = greater (suc i) zero
compare (suc i) (suc j) with compare i j
compare (suc ._) (suc .greatest) | less    greatest least =
                                                  less    (suc greatest) (suc least)
compare (suc .greatest) (suc ._) | greater greatest least =
                                                  greater (suc greatest) (suc least)
compare (suc .i)        (suc .i)              | equal i = equal (suc i)
-}
