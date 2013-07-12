-- NOTE with-K
open import Data.Bit hiding (_==_)
open import Data.Bits
open import Data.Two hiding (_==_)

-- TODO get rid of IFs
open import Data.Bool using (if_then_else_)

import Data.Fin as Fin
open Fin using (Fin; zero; suc; #_; inject₁; inject+; raise) renaming (_+_ to _+ᶠ_)
open import Data.Nat.NP hiding (_==_)
open import Data.Vec.NP
open import Data.Vec.Bijection
open import Data.Vec.Permutation

open import Function.Bijection.SyntaxKit
open import Function.NP

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡

module Data.Bits.OperationSyntax where

module 𝟚Bij = 𝟚Bijection
open 𝟚Bij public using (`id; 𝟚Bij) renaming (bool-bijKit to bitBijKit; `not to `notᴮ)
open BijectionSyntax Bit 𝟚Bij public
open BijectionSemantics bitBijKit public

{-
  id    ε          id
  0↔1   swp-inners interchange
  not   swap       comm
  when0 first      ...
  when1 second     ...
-}
`not : ∀ {n} → Bij (1 + n)
`not = 𝟚Bij.`not `∷ const `id

`xor : ∀ {n} → Bit → Bij (1 + n)
`xor b = 𝟚Bij.`xor b `∷ const `id

`[0:_1:_] : ∀ {n} → Bij n → Bij n → Bij (1 + n)
`[0: f 1: g ] = 𝟚Bij.`id `∷ [0: f 1: g ]

`when0 : ∀ {n} → Bij n → Bij (1 + n)
`when0 f = `[0: f    1: `id ]

`when1 : ∀ {n} → Bij n → Bij (1 + n)
`when1 f = `[0: `id  1:   f ]

-- law: `when0 f `⁏ `when1 g ≡ `when1 g `; `when0 f

on-firsts : ∀ {n} → Bij (1 + n) → Bij (2 + n)
on-firsts f = `0↔1 `⁏ `when0 f `⁏ `0↔1

--   (a · b) · (c · d)
-- ≡ right swap
--   (a · b) · (d · c)
-- ≡ interchange
--   (a · d) · (b · c)
-- ≡ right swap
--   (a · d) · (c · b)
swp-seconds : ∀ {n} → Bij (2 + n)
swp-seconds = `when1 `not `⁏ `0↔1 `⁏ `when1 `not

on-extremes : ∀ {n} → Bij (1 + n) → Bij (2 + n)
-- on-extremes f = swp-seconds `⁏ `when0 f `⁏ swp-seconds

-- (a · b) · (c · d)
-- ≡ right swap ≡ when1 not
-- (a · b) · (d · c)
-- ≡ interchange ≡ 0↔1
-- (a · d) · (b · c)
-- ≡ left f ≡ when0 f
-- (A · D) · (b · c)
--     where A · D = f (a · d)
-- ≡ interchange ≡ 0↔1
-- (A · b) · (D · c)
-- ≡ right swap ≡ when1 not
-- (A · b) · (c · D)
on-extremes f = `when1 `not `⁏ `0↔1 `⁏ `when0 f `⁏ `0↔1 `⁏ `when1 `not

map-inner : ∀ {n} → Bij (1 + n) → Bij (2 + n)
map-inner f = `when1 `not `⁏ `0↔1 `⁏ `when1 f `⁏ `0↔1 `⁏ `when1 `not

map-outer : ∀ {n} → Bij n → Bij n → Bij (1 + n)
map-outer = `[0:_1:_]

0↔1∷_ : ∀ {n} → Bits n → Bij (1 + n)
0↔1∷ [] = `not
0↔1∷ (0₂ ∷ p) = on-firsts   (0↔1∷ p)
0↔1∷ (1₂ ∷ p) = on-extremes (0↔1∷ p)

0↔_ : ∀ {n} → Bits n → Bij n
0↔ [] = `id
0↔ (0₂ ∷ p) = `when0 (0↔ p)
0↔ (1₂ ∷ p) = 0↔1∷ p

⟨0↔_⟩-sem : ∀ {n} (p : Bits n) → Bits n → Bits n
⟨0↔ p ⟩-sem xs = if 0ⁿ == xs then p else if p == xs then 0ⁿ else xs

if∷ : ∀ {n} a x (xs ys : Bits n) → (if a then (x ∷ xs) else (x ∷ ys)) ≡ x ∷ (if a then xs else ys)
if∷ 1₂ x xs ys = refl
if∷ 0₂ x xs ys = refl

if-not∷ : ∀ {n} a (xs ys : Bits n) → (if a then (0₂ ∷ xs) else (1₂ ∷ ys)) ≡ (not a) ∷ (if a then xs else ys)
if-not∷ 1₂ xs ys = refl
if-not∷ 0₂ xs ys = refl

if∷′ : ∀ {n} a (xs ys : Bits n) → (if a then (1₂ ∷ xs) else (0₂ ∷ ys)) ≡ a ∷ (if a then xs else ys)
if∷′ 1₂ xs ys = refl
if∷′ 0₂ xs ys = refl

⟨0↔1∷_⟩-spec : ∀ {n} (p : Bits n) xs → 0↔1∷ p · xs ≡ ⟨0↔ (1∷ p) ⟩-sem xs
⟨0↔1∷_⟩-spec [] (1₂ ∷ []) = refl
⟨0↔1∷_⟩-spec [] (0₂ ∷ []) = refl
⟨0↔1∷_⟩-spec (1₂ ∷ ps) (1₂ ∷ 1₂ ∷ xs)
   rewrite ⟨0↔1∷_⟩-spec ps (1∷ xs)
     with ps == xs
... | 1₂ = refl
... | 0₂ = refl
⟨0↔1∷_⟩-spec (1₂ ∷ ps) (1₂ ∷ 0₂ ∷ xs) = refl
⟨0↔1∷_⟩-spec (1₂ ∷ ps) (0₂ ∷ 1₂ ∷ xs) = refl
⟨0↔1∷_⟩-spec (1₂ ∷ ps) (0₂ ∷ 0₂ ∷ xs)
   rewrite ⟨0↔1∷_⟩-spec ps (0∷ xs)
     with 0ⁿ == xs
... | 1₂ = refl
... | 0₂ = refl
⟨0↔1∷_⟩-spec (0₂ ∷ ps) (1₂ ∷ 1₂ ∷ xs) = refl
⟨0↔1∷_⟩-spec (0₂ ∷ ps) (1₂ ∷ 0₂ ∷ xs)
   rewrite ⟨0↔1∷_⟩-spec ps (1∷ xs)
     with ps == xs
... | 1₂ = refl
... | 0₂ = refl
⟨0↔1∷_⟩-spec (0₂ ∷ ps) (0₂ ∷ 1₂ ∷ xs) = refl
⟨0↔1∷_⟩-spec (0₂ ∷ ps) (0₂ ∷ 0₂ ∷ xs)
   rewrite ⟨0↔1∷_⟩-spec ps (0∷ xs)
     with 0ⁿ == xs
... | 1₂ = refl
... | 0₂ = refl

⟨0↔_⟩-spec : ∀ {n} (p : Bits n) xs → 0↔ p · xs ≡ ⟨0↔ p ⟩-sem xs
⟨0↔_⟩-spec [] [] = refl
⟨0↔_⟩-spec (0₂ ∷ ps) (1₂ ∷ xs) = refl
⟨0↔_⟩-spec (0₂ ∷ ps) (0₂ ∷ xs)
  rewrite ⟨0↔ ps ⟩-spec xs
          | if∷ (ps == xs) 0b 0ⁿ xs
          | if∷ (0ⁿ == xs) 0b ps (if ps == xs then 0ⁿ else xs)
          = refl
⟨0↔_⟩-spec (1₂ ∷ p) xs = ⟨0↔1∷ p ⟩-spec xs

private
  module P where
    open PermutationSyntax public
    open PermutationSemantics public
open P using (Perm; `id; `0↔1; _`⁏_)

`⟨0↔1+_⟩ : ∀ {n} (i : Fin n) → Bij (1 + n)
`⟨0↔1+ zero  ⟩ = `0↔1
`⟨0↔1+ suc i ⟩ = `0↔1 `⁏ `tl `⟨0↔1+ i ⟩ `⁏ `0↔1

`⟨0↔1+_⟩-spec : ∀ {n} (i : Fin n) xs → `⟨0↔1+ i ⟩ · xs ≡ ⟨0↔1+ i ⟩ xs
`⟨0↔1+ zero  ⟩-spec xs = refl
`⟨0↔1+ suc i ⟩-spec (x ∷ _ ∷ xs) rewrite `⟨0↔1+ i ⟩-spec (x ∷ xs) = refl

`⟨0↔_⟩ : ∀ {n} (i : Fin n) → Bij n
`⟨0↔ zero  ⟩ = `id
`⟨0↔ suc i ⟩ = `⟨0↔1+ i ⟩

`⟨0↔_⟩-spec : ∀ {n} (i : Fin n) xs → `⟨0↔ i ⟩ · xs ≡ ⟨0↔ i ⟩ xs
`⟨0↔ zero  ⟩-spec xs = refl
`⟨0↔ suc i ⟩-spec xs = `⟨0↔1+ i ⟩-spec xs

{-
`⟨_↔_⟩ : ∀ {n} (i j : Fin n) → Bij n
`⟨ zero  ↔ j     ⟩ = `⟨0↔ j ⟩
`⟨ i     ↔ zero  ⟩ = `⟨0↔ i ⟩
`⟨ suc i ↔ suc j ⟩ = `tl `⟨ i ↔ j ⟩

`⟨_↔_⟩-spec : ∀ {n} (i j : Fin n) xs → `⟨ i ↔ j ⟩ · xs ≡ ⟨ i ↔ j ⟩ xs
`⟨_↔_⟩-spec zero    j       xs = `⟨0↔   j ⟩-spec xs
`⟨_↔_⟩-spec (suc i) zero    xs = `⟨0↔1+ i ⟩-spec xs
`⟨_↔_⟩-spec (suc i) (suc j) (x ∷ xs) rewrite `⟨ i ↔ j ⟩-spec xs = refl
-}

`xor-head : ∀ {n} → Bit → Bij (1 + n)
`xor-head = [0: `id   1: `not ]

`xor-head-spec : ∀ b {n} x (xs : Bits n) → `xor-head b · (x ∷ xs) ≡ (b xor x) ∷ xs
`xor-head-spec 1₂ x xs  = refl
`xor-head-spec 0₂ x xs = refl

`⟨_⊕⟩ : ∀ {n} → Bits n → Bij n
`⟨ []     ⊕⟩ = `id
`⟨ b ∷ xs ⊕⟩ = `xor-head b `⁏ `tl `⟨ xs ⊕⟩

`⟨_⊕⟩-spec : ∀ {n} (xs ys : Bits n) → `⟨ xs ⊕⟩ · ys ≡ xs ⊕ ys
`⟨ []         ⊕⟩-spec []       = refl
`⟨ 1₂  ∷ xs ⊕⟩-spec (y ∷ ys) rewrite `⟨ xs ⊕⟩-spec ys = refl
`⟨ 0₂ ∷ xs ⊕⟩-spec (y ∷ ys) rewrite `⟨ xs ⊕⟩-spec ys = refl

⊕-dist-0↔1 : ∀ {n} (pad : Bits n) x → 0↔1 pad ⊕ 0↔1 x ≡ 0↔1 (pad ⊕ x)
⊕-dist-0↔1 _           []          = refl
⊕-dist-0↔1 (_ ∷ [])    (_ ∷ [])    = refl
⊕-dist-0↔1 (_ ∷ _ ∷ _) (_ ∷ _ ∷ _) = refl
-- -}
-- -}
-- -}
