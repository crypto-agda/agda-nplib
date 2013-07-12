{-# OPTIONS --without-K #-}
open import Data.Bit hiding (_==_)
open import Data.Bits
open import Data.Bool.NP hiding (_==_)
import Data.Fin as Fin
open Fin using (Fin; zero; suc; #_; inject₁; inject+; raise) renaming (_+_ to _+ᶠ_)
open import Data.Nat.NP hiding (_==_)
open import Data.Vec.NP

open import Function.Bijection.SyntaxKit
open import Function.NP

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡

module Data.Bits.OperationSyntax where

module BitBij = BoolBijection
open BitBij public using (`id) renaming (BoolBij to BitBij; bool-bijKit to bitBijKit; `not to `notᴮ)
open BijectionSyntax Bit BitBij public
open BijectionSemantics bitBijKit public

{-
  id   ε          id
  0↔1  swp-inners interchange
  not  swap       comm
  if0  first      ...
  if1  second     ...
-}
`not : ∀ {n} → Bij (1 + n)
`not = BitBij.`not `∷ const `id

`xor : ∀ {n} → Bit → Bij (1 + n)
`xor b = BitBij.`xor b `∷ const `id

`if : ∀ {n} → Bij n → Bij n → Bij (1 + n)
`if f g = BitBij.`id `∷ cond f g

`if0 : ∀ {n} → Bij n → Bij (1 + n)
`if0 f = `if `id f

`if1 : ∀ {n} → Bij n → Bij (1 + n)
`if1 f = `if f `id

-- law: `if0 f `⁏ `if1 g ≡ `if1 g `; `if0 f

on-firsts : ∀ {n} → Bij (1 + n) → Bij (2 + n)
on-firsts f = `0↔1 `⁏ `if0 f `⁏ `0↔1

--   (a ∙ b) ∙ (c ∙ d)
-- ≡ right swap
--   (a ∙ b) ∙ (d ∙ c)
-- ≡ interchange
--   (a ∙ d) ∙ (b ∙ c)
-- ≡ right swap
--   (a ∙ d) ∙ (c ∙ b)
swp-seconds : ∀ {n} → Bij (2 + n)
swp-seconds = `if1 `not `⁏ `0↔1 `⁏ `if1 `not

on-extremes : ∀ {n} → Bij (1 + n) → Bij (2 + n)
-- on-extremes f = swp-seconds `⁏ `if0 f `⁏ swp-seconds

-- (a ∙ b) ∙ (c ∙ d)
-- ≡ right swap ≡ if1 not
-- (a ∙ b) ∙ (d ∙ c)
-- ≡ interchange ≡ 0↔1
-- (a ∙ d) ∙ (b ∙ c)
-- ≡ left f ≡ if0 f
-- (A ∙ D) ∙ (b ∙ c)
--     where A ∙ D = f (a ∙ d)
-- ≡ interchange ≡ 0↔1
-- (A ∙ b) ∙ (D ∙ c)
-- ≡ right swap ≡ if1 not
-- (A ∙ b) ∙ (c ∙ D)
on-extremes f = `if1 `not `⁏ `0↔1 `⁏ `if0 f `⁏ `0↔1 `⁏ `if1 `not

map-inner : ∀ {n} → Bij (1 + n) → Bij (2 + n)
map-inner f = `if1 `not `⁏ `0↔1 `⁏ `if1 f `⁏ `0↔1 `⁏ `if1 `not

map-outer : ∀ {n} → Bij n → Bij n → Bij (1 + n)
map-outer f g = `if g f

0↔1∷_ : ∀ {n} → Bits n → Bij (1 + n)
0↔1∷ [] = `not
0↔1∷ (true {-1-} ∷ p) = on-extremes (0↔1∷ p)
0↔1∷ (false{-0-} ∷ p) = on-firsts   (0↔1∷ p)

0↔_ : ∀ {n} → Bits n → Bij n
0↔ [] = `id
0↔ (false{-0-} ∷ p) = `if0 (0↔ p)
0↔ (true{-1-}  ∷ p) = 0↔1∷ p

⟨0↔_⟩-sem : ∀ {n} (p : Bits n) → Bits n → Bits n
⟨0↔ p ⟩-sem xs = if 0ⁿ == xs then p else if p == xs then 0ⁿ else xs

if∷ : ∀ {n} a x (xs ys : Bits n) → (if a then (x ∷ xs) else (x ∷ ys)) ≡ x ∷ (if a then xs else ys)
if∷ true x xs ys = refl
if∷ false x xs ys = refl

if-not∷ : ∀ {n} a (xs ys : Bits n) → (if a then (false ∷ xs) else (true ∷ ys)) ≡ (not a) ∷ (if a then xs else ys)
if-not∷ true xs ys = refl
if-not∷ false xs ys = refl

if∷′ : ∀ {n} a (xs ys : Bits n) → (if a then (true ∷ xs) else (false ∷ ys)) ≡ a ∷ (if a then xs else ys)
if∷′ true xs ys = refl
if∷′ false xs ys = refl

⟨0↔1∷_⟩-spec : ∀ {n} (p : Bits n) xs → 0↔1∷ p ∙ xs ≡ ⟨0↔ (1∷ p) ⟩-sem xs
⟨0↔1∷_⟩-spec [] (true ∷ []) = refl
⟨0↔1∷_⟩-spec [] (false ∷ []) = refl
⟨0↔1∷_⟩-spec (true ∷ ps) (true ∷ true ∷ xs)
   rewrite ⟨0↔1∷_⟩-spec ps (1∷ xs)
     with ps == xs
... | true = refl
... | false = refl
⟨0↔1∷_⟩-spec (true ∷ ps) (true ∷ false ∷ xs) = refl
⟨0↔1∷_⟩-spec (true ∷ ps) (false ∷ true ∷ xs) = refl
⟨0↔1∷_⟩-spec (true ∷ ps) (false ∷ false ∷ xs)
   rewrite ⟨0↔1∷_⟩-spec ps (0∷ xs)
     with 0ⁿ == xs
... | true = refl
... | false = refl
⟨0↔1∷_⟩-spec (false ∷ ps) (true ∷ true ∷ xs) = refl
⟨0↔1∷_⟩-spec (false ∷ ps) (true ∷ false ∷ xs)
   rewrite ⟨0↔1∷_⟩-spec ps (1∷ xs)
     with ps == xs
... | true = refl
... | false = refl
⟨0↔1∷_⟩-spec (false ∷ ps) (false ∷ true ∷ xs) = refl
⟨0↔1∷_⟩-spec (false ∷ ps) (false ∷ false ∷ xs)
   rewrite ⟨0↔1∷_⟩-spec ps (0∷ xs)
     with 0ⁿ == xs
... | true = refl
... | false = refl

⟨0↔_⟩-spec : ∀ {n} (p : Bits n) xs → 0↔ p ∙ xs ≡ ⟨0↔ p ⟩-sem xs
⟨0↔_⟩-spec [] [] = refl
⟨0↔_⟩-spec (false ∷ ps) (true ∷ xs) = refl
⟨0↔_⟩-spec (false ∷ ps) (false ∷ xs)
  rewrite ⟨0↔ ps ⟩-spec xs
          | if∷ (ps == xs) 0b 0ⁿ xs
          | if∷ (0ⁿ == xs) 0b ps (if ps == xs then 0ⁿ else xs)
          = refl
⟨0↔_⟩-spec (true ∷ p) xs = ⟨0↔1∷ p ⟩-spec xs

private
  module P where
    open PermutationSyntax public
    open PermutationSemantics public
open P using (Perm; `id; `0↔1; _`⁏_)

`⟨0↔1+_⟩ : ∀ {n} (i : Fin n) → Bij (1 + n)
`⟨0↔1+ zero  ⟩ = `0↔1
`⟨0↔1+ suc i ⟩ = `0↔1 `⁏ `tl `⟨0↔1+ i ⟩ `⁏ `0↔1

`⟨0↔1+_⟩-spec : ∀ {n} (i : Fin n) xs → `⟨0↔1+ i ⟩ ∙ xs ≡ ⟨0↔1+ i ⟩ xs
`⟨0↔1+ zero  ⟩-spec xs = refl
`⟨0↔1+ suc i ⟩-spec (x ∷ _ ∷ xs) rewrite `⟨0↔1+ i ⟩-spec (x ∷ xs) = refl

`⟨0↔_⟩ : ∀ {n} (i : Fin n) → Bij n
`⟨0↔ zero  ⟩ = `id
`⟨0↔ suc i ⟩ = `⟨0↔1+ i ⟩

`⟨0↔_⟩-spec : ∀ {n} (i : Fin n) xs → `⟨0↔ i ⟩ ∙ xs ≡ ⟨0↔ i ⟩ xs
`⟨0↔ zero  ⟩-spec xs = refl
`⟨0↔ suc i ⟩-spec xs = `⟨0↔1+ i ⟩-spec xs

{-
`⟨_↔_⟩ : ∀ {n} (i j : Fin n) → Bij n
`⟨ zero  ↔ j     ⟩ = `⟨0↔ j ⟩
`⟨ i     ↔ zero  ⟩ = `⟨0↔ i ⟩
`⟨ suc i ↔ suc j ⟩ = `tl `⟨ i ↔ j ⟩

`⟨_↔_⟩-spec : ∀ {n} (i j : Fin n) xs → `⟨ i ↔ j ⟩ ∙ xs ≡ ⟨ i ↔ j ⟩ xs
`⟨_↔_⟩-spec zero    j       xs = `⟨0↔   j ⟩-spec xs
`⟨_↔_⟩-spec (suc i) zero    xs = `⟨0↔1+ i ⟩-spec xs
`⟨_↔_⟩-spec (suc i) (suc j) (x ∷ xs) rewrite `⟨ i ↔ j ⟩-spec xs = refl
-}

`xor-head : ∀ {n} → Bit → Bij (1 + n)
`xor-head b = if b then `not else `id

`xor-head-spec : ∀ b {n} x (xs : Bits n) → `xor-head b ∙ (x ∷ xs) ≡ (b xor x) ∷ xs
`xor-head-spec true x xs  = refl
`xor-head-spec false x xs = refl

`⟨_⊕⟩ : ∀ {n} → Bits n → Bij n
`⟨ []     ⊕⟩ = `id
`⟨ b ∷ xs ⊕⟩ = `xor-head b `⁏ `tl `⟨ xs ⊕⟩

`⟨_⊕⟩-spec : ∀ {n} (xs ys : Bits n) → `⟨ xs ⊕⟩ ∙ ys ≡ xs ⊕ ys
`⟨ []         ⊕⟩-spec []       = refl
`⟨ true  ∷ xs ⊕⟩-spec (y ∷ ys) rewrite `⟨ xs ⊕⟩-spec ys = refl
`⟨ false ∷ xs ⊕⟩-spec (y ∷ ys) rewrite `⟨ xs ⊕⟩-spec ys = refl

⊕-dist-0↔1 : ∀ {n} (pad : Bits n) x → 0↔1 pad ⊕ 0↔1 x ≡ 0↔1 (pad ⊕ x)
⊕-dist-0↔1 _           []          = refl
⊕-dist-0↔1 (_ ∷ [])    (_ ∷ [])    = refl
⊕-dist-0↔1 (_ ∷ _ ∷ _) (_ ∷ _ ∷ _) = refl
