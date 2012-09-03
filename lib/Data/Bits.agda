module Data.Bits where

-- cleanup
import Level
open import Category.Applicative.NP
open import Category.Monad
open import Data.Nat.NP hiding (_==_) renaming (_<=_ to _ℕ<=_)
open import Data.Nat.Properties
open import Data.Nat.DivMod
import Data.Bool.NP as Bool
open Bool hiding (_==_; toℕ)
open import Data.Bool.Properties using (not-involutive)
open import Data.Maybe.NP
import Data.Fin as Fin
open Fin using (Fin; zero; suc; #_; inject₁; inject+; raise) renaming (_+_ to _+ᶠ_)
import Data.Vec.NP as V
open V hiding (rewire; rewireTbl; sum) renaming (map to vmap; swap to vswap)
open import Data.Vec.N-ary.NP
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; uncurry; proj₁; proj₂)
open import Function.NP hiding (_→⟨_⟩_)
open import Relation.Nullary
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡
open import Algebra.FunctionProperties.NP
import Data.List.NP as L
open import Function.Bijection.SyntaxKit

open import Data.Bool.NP public using (_xor_; not; true; false; if_then_else_)
open V public using ([]; _∷_; head; tail; replicate; RewireTbl)

Bit : Set
Bit = Bool

module Defs where
  0b = false
  1b = true
module Patterns where
  pattern 0b = false
  pattern 1b = true
open Patterns

Bits : ℕ → Set
Bits = Vec Bit

_→ᵇ_ : ℕ → ℕ → Set
i →ᵇ o = Bits i → Bits o

0ⁿ : ∀ {n} → Bits n
0ⁿ = replicate 0b

-- Warning: 0ⁿ {0} ≡ 1ⁿ {0}
1ⁿ : ∀ {n} → Bits n
1ⁿ = replicate 1b

0∷_ : ∀ {n} → Bits n → Bits (suc n)
0∷ xs = 0b ∷ xs

-- can't we make these pattern aliases?
1∷_ : ∀ {n} → Bits n → Bits (suc n)
1∷ xs = 1b ∷ xs

_!_ : ∀ {a n} {A : Set a} → Vec A n → Fin n → A
_!_ = flip lookup

_==ᵇ_ : (b₀ b₁ : Bit) → Bool
b₀ ==ᵇ b₁ = not (b₀ xor b₁)

_==_ : ∀ {n} (bs₀ bs₁ : Bits n) → Bool
[] == [] = true
(b₀ ∷ bs₀) == (b₁ ∷ bs₁) = (b₀ ==ᵇ b₁) ∧ bs₀ == bs₁

==-comm : ∀ {n} (xs ys : Bits n) → xs == ys ≡ ys == xs
==-comm [] [] = refl
==-comm (x ∷ xs) (x₁ ∷ ys) rewrite Xor°.+-comm x x₁ | ==-comm xs ys = refl

==-refl : ∀ {n} (xs : Bits n) → (xs == xs) ≡ 1b
==-refl [] = refl
==-refl (true ∷ xs) = ==-refl xs
==-refl (false ∷ xs) = ==-refl xs

_<=_ : ∀ {n} (xs ys : Bits n) → Bool
[]        <= []        = 1b
(1b ∷ xs) <= (0b ∷ ys) = 0b
(0b ∷ xs) <= (1b ∷ ys) = 1b
(_  ∷ xs) <= (_  ∷ ys) = xs <= ys

infixr 5 _⊕_
_⊕_ : ∀ {n} (bs₀ bs₁ : Bits n) → Bits n
_⊕_ = zipWith _xor_

-- Negate all bits, i.e. "xor"ing them by one.
vnot : ∀ {n} → Endo (Bits n)
vnot = _⊕_ 1ⁿ

vnot∘vnot≗id : ∀ {n} → vnot {n} ∘ vnot ≗ id
vnot∘vnot≗id [] = refl
vnot∘vnot≗id (x ∷ xs) rewrite not-involutive x | vnot∘vnot≗id xs = refl

-- Negate the i-th bit.
notᵢ : ∀ {n} (i : Fin n) → Bits n → Bits n
notᵢ = onᵢ not

⊕-assoc : ∀ {n} → Associative _≡_ (_⊕_ {n})
⊕-assoc [] [] [] = refl
⊕-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite ⊕-assoc xs ys zs | Xor°.+-assoc x y z = refl

⊕-comm  : ∀ {n} → Commutative _≡_ (_⊕_ {n})
⊕-comm [] [] = refl
⊕-comm (x ∷ xs) (y ∷ ys) rewrite ⊕-comm xs ys | Xor°.+-comm x y = refl

⊕-left-identity : ∀ {n} → LeftIdentity _≡_ 0ⁿ (_⊕_ {n})
⊕-left-identity [] = refl
⊕-left-identity (x ∷ xs) rewrite ⊕-left-identity xs = refl

⊕-right-identity : ∀ {n} → RightIdentity _≡_ 0ⁿ (_⊕_ {n})
⊕-right-identity [] = refl
⊕-right-identity (x ∷ xs) rewrite ⊕-right-identity xs | proj₂ Xor°.+-identity x = refl

⊕-≡ : ∀ {n} (x : Bits n) → x ⊕ x ≡ 0ⁿ
⊕-≡ [] = refl
⊕-≡ (x ∷ xs) rewrite ⊕-≡ xs | proj₂ Xor°.-‿inverse x = refl

⊕-≢ : ∀ {n} (x : Bits n) → x ⊕ vnot x ≡ 1ⁿ
⊕-≢ x = x ⊕ vnot x   ≡⟨ refl ⟩
         x ⊕ (1ⁿ ⊕ x) ≡⟨ cong (_⊕_ x) (⊕-comm 1ⁿ x) ⟩
         x ⊕ (x ⊕ 1ⁿ) ≡⟨ sym (⊕-assoc x x 1ⁿ) ⟩
         (x ⊕ x) ⊕ 1ⁿ ≡⟨ cong (flip _⊕_ 1ⁿ) (⊕-≡ x) ⟩
         0ⁿ ⊕ 1ⁿ       ≡⟨ ⊕-left-identity 1ⁿ ⟩
         1ⁿ ∎ where open ≡-Reasoning

-- "Xor"ing the i-th bit with `b' is the same thing as "xor"ing with a vector of zeros
-- except at the i-th position.
-- Such a vector can be obtained by "xor"ing the i-th bit of a vector of zeros.
onᵢ-xor-⊕ : ∀ b {n} (i : Fin n) → onᵢ (_xor_ b) i ≗ _⊕_ (onᵢ (_xor_ b) i 0ⁿ)
onᵢ-xor-⊕ b zero    (x ∷ xs) rewrite proj₂ Xor°.+-identity b | ⊕-left-identity xs = refl
onᵢ-xor-⊕ b (suc i) (x ∷ xs) rewrite onᵢ-xor-⊕ b i xs = refl

msb : ∀ k {n} → Bits (k + n) → Bits k
msb = take

lsb : ∀ {n} k → Bits (n + k) → Bits k
lsb {n} k rewrite ℕ°.+-comm n k = reverse ∘ msb k ∘ reverse

msb₂ : ∀ {n} → Bits (2 + n) → Bits 2
msb₂ = msb 2

lsb₂ : ∀ {n} → Bits (2 + n) → Bits 2
lsb₂ = reverse ∘ msb 2 ∘ reverse

#1 : ∀ {n} → Bits n → Fin (suc n)
#1 [] = zero
#1 (0b ∷ bs) = inject₁ (#1 bs)
#1 (1b ∷ bs) = suc (#1 bs)

#0 : ∀ {n} → Bits n → Fin (suc n)
#0 = #1 ∘ vmap not

allBitsL : ∀ n → L.List (Bits n)
allBitsL _ = replicateM (toList (0b ∷ 1b ∷ []))
  where open L.Monad

allBits : ∀ n → Vec (Bits n) (2^ n)
allBits zero    = [] ∷ []
allBits (suc n) = vmap 0∷_ bs ++ vmap 1∷_ bs
  where bs = allBits n

always : ∀ n → Bits n → Bit
always _ _ = 1b
never  : ∀ n → Bits n → Bit
never _ _ = 0b

_|∨|_ : ∀ {n} → (f g : Bits n → Bit) → Bits n → Bit
_|∨|_ f g x = f x ∨ g x

_|∧|_ : ∀ {n} → (f g : Bits n → Bit) → Bits n → Bit
_|∧|_ f g x = f x ∧ g x

|not| : ∀ {n} (f : Bits n → Bit) → Bits n → Bit
|not| f = not ∘ f

|∧|-comm : ∀ {n} (f g : Bits n → Bit) → f |∧| g ≗ g |∧| f
|∧|-comm f g x with f x | g x
... | 0b | 0b = refl
... | 0b | 1b = refl
... | 1b | 0b = refl
... | 1b | 1b = refl

module Search {i} {I : Set i} (`1 : I) (`2*_ : I → I)
              {a} {A : I → Set a} (_∙_ : ∀ {m} → A m → A m → A (`2* m)) where

  `2^_ : ℕ → I
  `2^_ = fold `1 `2*_

  search : ∀ {n} → (Bits n → A `1) → A (`2^ n)
  search {zero}  f = f []
  search {suc n} f = search (f ∘ 0∷_) ∙ search (f ∘ 1∷_)

  searchBit : (Bit → A `1) → A (`2* `1)
  searchBit f = f 0b ∙ f 1b

  -- search-ext
  search-≗ : ∀ {n} (f g : Bits n → A `1) → f ≗ g → search f ≡ search g
  search-≗ {zero}  f g f≗g = f≗g []
  search-≗ {suc n} f g f≗g
    rewrite search-≗ (f ∘ 0∷_) (g ∘ 0∷_) (f≗g ∘ 0∷_)
          | search-≗ (f ∘ 1∷_) (g ∘ 1∷_) (f≗g ∘ 1∷_) = refl

  module Comm (∙-comm : ∀ {m} (x y : A m) → x ∙ y ≡ y ∙ x) where

    {- This pad bit vector allows to specify which bit do we negate in the vector. -}
    search-comm : ∀ {n} (pad : Bits n) (f : Bits n → A `1) → search f ≡ search (f ∘ _⊕_ pad)
    search-comm {zero} pad f = refl
    search-comm {suc n} (b ∷ pad) f
      rewrite search-comm pad (f ∘ 0∷_)
            | search-comm pad (f ∘ 1∷_)
      with b
    ... | true  = ∙-comm (search (f ∘ 0∷_ ∘ _⊕_ pad)) _
    ... | false = refl
  open Comm public

open Search 1 2*_ public using () renaming (search to search′; search-≗ to search′-≗; search-comm to search′-comm)

module OperationSyntax where
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

module PermutationSyntax-Props where
    open PermutationSyntax
    open PermutationSemantics
    -- open PermutationProperties

    ⊕-dist-0↔1 : ∀ {n} (pad : Bits n) xs → 0↔1 pad ⊕ 0↔1 xs ≡ 0↔1 (pad ⊕ xs)
    ⊕-dist-0↔1 _           []          = refl
    ⊕-dist-0↔1 (_ ∷ [])    (_ ∷ [])    = refl
    ⊕-dist-0↔1 (_ ∷ _ ∷ _) (_ ∷ _ ∷ _) = refl

    -- TODO make use of ⊛-dist-∙
    ⊕-dist-∙ : ∀ {n} (pad : Bits n) π xs → π ∙ pad ⊕ π ∙ xs ≡ π ∙ (pad ⊕ xs)
    ⊕-dist-∙ fs      `id        xs = refl
    ⊕-dist-∙ fs      `0↔1       xs = ⊕-dist-0↔1 fs xs
    ⊕-dist-∙ (f ∷ fs) (`tl π)   (x ∷ xs) rewrite ⊕-dist-∙ fs π xs = refl
    ⊕-dist-∙ fs       (π₀ `⁏ π₁) xs rewrite ⊕-dist-∙ (π₀ ∙ fs) π₁ (π₀ ∙ xs)
                                         | ⊕-dist-∙ fs π₀ xs = refl
    {-
 -- ⊛-dist-∙ : ∀ {n a} {A : Set a} (fs : Vec (A → A) n) π xs → π ∙ fs ⊛ π ∙ xs ≡ π ∙ (fs ⊛ xs)
    ⊕-dist-∙ : ∀ {n} (pad : Bits n) π xs → π ∙ pad ⊕ π ∙ xs ≡ π ∙ (pad ⊕ xs)
    ⊕-dist-∙ pad π xs = π ∙ pad ⊕ π ∙ xs
                      ≡⟨ refl ⟩
                        vmap _xor_ (π ∙ pad) ⊛ π ∙ xs
                      ≡⟨ TODO ⟩
                        π ∙ vmap _xor_ pad ⊛ π ∙ xs
                      ≡⟨ ⊛-dist-∙ _ (vmap _xor_ pad) π xs ⟩
                        π ∙ (vmap _xor_ pad ⊛ xs)
                      ≡⟨ refl ⟩
                        π ∙ (pad ⊕ xs)
                      ∎ where open ≡-Reasoning
     -- rans {!⊛-dist-∙ (vmap _xor_ (op ∙ pad)) op xs!} (⊛-dist-∙ (vmap _xor_ pad) op xs)
-}
module SimpleSearch {a} {A : Set a} (_∙_ : A → A → A) where

    open Search 1 2*_ {A = const A} _∙_ public

    module SearchUnit ε (ε∙ε : ε ∙ ε ≡ ε) where
        search-constε≡ε : ∀ n → search {n = n} (const ε) ≡ ε
        search-constε≡ε zero = refl
        search-constε≡ε (suc n) rewrite search-constε≡ε n = ε∙ε

    searchBit-search : ∀ n (f : Bits (suc n) → A) → searchBit (λ b → search (f ∘ _∷_ b)) ≡ search f
    searchBit-search n f = refl

    search-≗₂ : ∀ {m n} (f g : Bits m → Bits n → A) → f ≗₂ g
                  → search (search ∘ f) ≡ search (search ∘ g)
    search-≗₂ f g f≗g = search-≗ (search ∘ f) (search ∘ g) (λ xs →
                          search-≗ (f xs) (g xs) (λ ys →
                            f≗g xs ys))

    search-+ : ∀ {m n} (f : Bits (m + n) → A) →
                 search {m + n} f
               ≡ search {m} (λ xs → search {n} (λ ys → f (xs ++ ys)))
    search-+ {zero} f = refl
    search-+ {suc m} f rewrite search-+ {m} (f ∘ 0∷_)
                             | search-+ {m} (f ∘ 1∷_) = refl

    module SearchInterchange (∙-interchange : Interchange _≡_ _∙_ _∙_) where

        search-dist : ∀ {n} (f₀ f₁ : Bits n → A) → search (λ x → f₀ x ∙ f₁ x) ≡ search f₀ ∙ search f₁
        search-dist {zero}  _ _ = refl
        search-dist {suc n} f₀ f₁
          rewrite search-dist (f₀ ∘ 0∷_) (f₁ ∘ 0∷_)
                | search-dist (f₀ ∘ 1∷_) (f₁ ∘ 1∷_)
                = ∙-interchange _ _ _ _

        search-searchBit : ∀ {n} (f : Bits (suc n) → A) →
                             search (λ xs → searchBit (λ b → f (b ∷ xs))) ≡ search f
        search-searchBit f = search-dist (f ∘ 0∷_) (f ∘ 1∷_)

        search-search : ∀ {m n} (f : Bits (m + n) → A) →
                          search {m} (λ xs → search {n} (λ ys → f (xs ++ ys)))
                        ≡ search {n} (λ ys → search {m} (λ xs → f (xs ++ ys)))
        search-search {zero} f = refl
        search-search {suc m} {n} f
          rewrite search-search {m} {n} (f ∘ 0∷_)
                | search-search {m} {n} (f ∘ 1∷_)
                | search-searchBit {n} (λ { (b ∷ ys) → search {m} (λ xs → f (b ∷ xs ++ ys)) })
                = refl
        {- -- It might also be done by using search-dist twice and commutativity of addition.
           -- However, this also affect 'f' and makes this proof actually longer.
           search-search {m} {n} f =
                             search {m} (λ xs → search {n} (λ ys → f (xs ++ ys)))
                           ≡⟨ {!!} ⟩
                             search {m + n} f
                           ≡⟨ {!!} ⟩
                             search {n + m} (f ∘ vswap n)
                           ≡⟨ {!!} ⟩
                             search {n} (λ ys → search {m} (λ xs → f (vswap n (ys ++ xs))))
                           ≡⟨ {!!} ⟩
                             search {n} (λ ys → search {m} (λ xs → f (xs ++ ys)))
                           ∎
                           where open ≡-Reasoning
         -}

        search-swap : ∀ {m n} (f : Bits (m + n) → A) → search {n + m} (f ∘ vswap n) ≡ search {m + n} f
        search-swap {m} {n} f =
                     search {n + m} (f ∘ vswap n)
                   ≡⟨ search-+ {n} {m} (f ∘ vswap n) ⟩
                     search {n} (λ ys → search {m} (λ xs → f (vswap n (ys ++ xs))))
                   ≡⟨ search-≗₂ {n} {m}
                                (λ ys → f ∘ vswap n ∘ _++_ ys)
                                (λ ys → f ∘ flip _++_ ys)
                                (λ ys xs → cong f (swap-++ n ys xs)) ⟩
                     search {n} (λ ys → search {m} (λ xs → f (xs ++ ys)))
                   ≡⟨ sym (search-search {m} {n} f) ⟩
                     search {m} (λ xs → search {n} (λ ys → f (xs ++ ys)))
                   ≡⟨ sym (search-+ {m} {n} f) ⟩
                     search {m + n} f
                   ∎ where open ≡-Reasoning

        search-0↔1 : ∀ {n} (f : Bits n → A) → search {n} (f ∘ 0↔1) ≡ search {n} f
        search-0↔1 {zero}        _ = refl
        search-0↔1 {suc zero}    _ = refl
        search-0↔1 {suc (suc n)} _ = ∙-interchange _ _ _ _

    module Bij (∙-comm : Commutative _≡_ _∙_)
              (∙-interchange : Interchange _≡_ _∙_ _∙_) where
        open SearchInterchange ∙-interchange using (search-0↔1)
        open OperationSyntax hiding (_∙_)
        search-bij : ∀ {n} f (g : Bits n → A) → search (g ∘ eval f) ≡ search g
        search-bij `id     _ = refl
        search-bij `0↔1    f = search-0↔1 f
        search-bij (f `⁏ g) h
          rewrite search-bij f (h ∘ eval g)
                | search-bij g h
                = refl
        search-bij {suc n} (`id   `∷ f) g
          rewrite search-bij (f 0b) (g ∘ 0∷_)
                | search-bij (f 1b) (g ∘ 1∷_)
                = refl
        search-bij {suc n} (`notᴮ `∷ f) g
          rewrite search-bij (f 1b) (g ∘ 0∷_)
                | search-bij (f 0b) (g ∘ 1∷_)
                = ∙-comm _ _

module Sum where
    open SimpleSearch _+_ using (module Comm; module SearchInterchange; module SearchUnit; module Bij)
    open SimpleSearch _+_ public using () renaming (search to sum; search-≗ to sum-≗; searchBit to sumBit;
                                                    search-≗₂ to sum-≗₂;
                                                    search-+ to sum-+)
    open Comm ℕ°.+-comm public renaming (search-comm to sum-comm)
    open SearchUnit 0 refl public renaming
       (search-constε≡ε to sum-const0≡0)
    open SearchInterchange +-interchange public renaming (
        search-dist to sum-dist;
        search-searchBit to sum-sumBit;
        search-search to sum-sum;
        search-swap to sum-swap)
    open Bij ℕ°.+-comm +-interchange public renaming (search-bij to sum-bij)

    sum-const : ∀ n x → sum {n} (const x) ≡ ⟨2^ n * x ⟩
    sum-const zero    _ = refl
    sum-const (suc n) x = cong₂ _+_ (sum-const n x) (sum-const n x)

#⟨_⟩ᶠ : ∀ {n} → (Bits n → Bool) → Fin (suc (2^ n))
#⟨ pred ⟩ᶠ = countᶠ pred (allBits _)

module Count where
    open Sum
    open OperationSyntax

    #⟨_⟩ : ∀ {n} → (Bits n → Bool) → ℕ
    #⟨ pred ⟩ = sum (Bool.toℕ ∘ pred)

    -- #-ext
    #-≗ : ∀ {n} (f g : Bits n → Bool) → f ≗ g → #⟨ f ⟩ ≡ #⟨ g ⟩
    #-≗ f g f≗g = sum-≗ (Bool.toℕ ∘ f) (Bool.toℕ ∘ g) (λ x → ≡.cong Bool.toℕ (f≗g x))

    #-comm : ∀ {n} (pad : Bits n) (f : Bits n → Bool) → #⟨ f ⟩ ≡ #⟨ f ∘ _⊕_ pad ⟩
    #-comm pad f = sum-comm pad (Bool.toℕ ∘ f)

    #-bij : ∀ {n} f (g : Bits n → Bit) → #⟨ g ∘ eval f ⟩ ≡ #⟨ g ⟩
    #-bij f g = sum-bij f (Bool.toℕ ∘ g)

    #-⊕ : ∀ {c} (bs : Bits c) (f : Bits c → Bit) → #⟨ f ⟩ ≡ #⟨ f ∘ _⊕_ bs ⟩
    #-⊕ = #-comm

    #-const : ∀ n b → #⟨ (λ (_ : Bits n) → b) ⟩ ≡ ⟨2^ n * Bool.toℕ b ⟩
    #-const n b = sum-const n (Bool.toℕ b)

    #never≡0 : ∀ n → #⟨ never n ⟩ ≡ 0
    #never≡0 = sum-const0≡0

    #always≡2^_ : ∀ n → #⟨ always n ⟩ ≡ 2^ n
    #always≡2^ n = sum-const n 1

    #-dist : ∀ {n} (f₀ f₁ : Bits n → Bit) → sum (λ x → Bool.toℕ (f₀ x) + Bool.toℕ (f₁ x)) ≡ #⟨ f₀ ⟩ + #⟨ f₁ ⟩
    #-dist f₀ f₁ = sum-dist (Bool.toℕ ∘ f₀) (Bool.toℕ ∘ f₁)

    #-+ : ∀ {m n} (f : Bits (m + n) → Bit) →
                     #⟨ f ⟩ ≡ sum {m} (λ xs → #⟨ (λ ys → f (xs ++ ys)) ⟩ )
    #-+ {m} {n} f = sum-+ {m} {n} (Bool.toℕ ∘ f)

    #-# : ∀ {m n} (f : Bits (m + n) → Bit) →
                          sum {m} (λ xs → #⟨ (λ ys → f (xs ++ ys)) ⟩)
                        ≡ sum {n} (λ ys → #⟨ (λ (xs : Bits m) → f (xs ++ ys)) ⟩)
    #-# {m} {n} f = sum-sum {m} {n} (Bool.toℕ ∘ f)

    #-swap : ∀ {m n} (f : Bits (m + n) → Bit) → #⟨ f ∘ vswap n {m} ⟩ ≡ #⟨ f ⟩
    #-swap {m} {n} f = sum-swap {m} {n} (Bool.toℕ ∘ f)

    #⟨==_⟩ : ∀ {n} (xs : Bits n) → #⟨ _==_ xs ⟩ ≡ 1
    #⟨== [] ⟩ = refl
    #⟨==_⟩ {suc n} (true ∷ xs)  rewrite #never≡0 n | #⟨== xs ⟩ = refl
    #⟨==_⟩ {suc n} (false ∷ xs) rewrite #never≡0 n | #⟨== xs ⟩ = refl

    ≗-cong-# : ∀ {n} (f g : Bits n → Bit) → f ≗ g → #⟨ f ⟩ ≡ #⟨ g ⟩
    ≗-cong-# f g f≗g = sum-≗ _ _ (cong Bool.toℕ ∘ f≗g)

    -- #-+ : ∀ {n a b} (f : Bits (suc n) → Bit) → #⟨ f ∘ 0∷_ ⟩ ≡ a → #⟨ f ∘ 1∷_ ⟩ ≡ b → #⟨ f ⟩ ≡ a + b
    -- #-+ f f0 f1 rewrite f0 | f1 = refl

    #-take-drop : ∀ m n (f : Bits m → Bit) (g : Bits n → Bit)
                    → #⟨ (f ∘ take m) |∧| (g ∘ drop m) ⟩ ≡ #⟨ f ⟩ * #⟨ g ⟩
    #-take-drop zero n f g with f []
    ... | true rewrite ℕ°.+-comm #⟨ g ⟩ 0 = refl
    ... | false = #never≡0 n
    #-take-drop (suc m) n f g
      rewrite ≗-cong-# ((f ∘ take (suc m)) |∧| (g ∘ drop (suc m)) ∘ 0∷_)
                       ((f ∘ 0∷_ ∘ take m) |∧| (g ∘ drop m))
                       (λ x → cong₂ (λ x y → f x ∧ g y) (take-∷ m 0b x) (drop-∷ m 0b x))
            | #-take-drop m n (f ∘ 0∷_) g
            | ≗-cong-# ((f ∘ take (suc m)) |∧| (g ∘ drop (suc m)) ∘ 1∷_)
                       ((f ∘ 1∷_ ∘ take m) |∧| (g ∘ drop m))
                       (λ x → cong₂ (λ x y → f x ∧ g y) (take-∷ m 1b x) (drop-∷ m 1b x))
            | #-take-drop m n (f ∘ 1∷_) g
            = sym (proj₂ ℕ°.distrib #⟨ g ⟩ #⟨ f ∘ 0∷_ ⟩ #⟨ f ∘ 1∷_ ⟩)

    #-drop-take : ∀ m n (f : Bits n → Bit) (g : Bits m → Bit)
                    → #⟨ (f ∘ drop m) |∧| (g ∘ take m) ⟩ ≡ #⟨ f ⟩ * #⟨ g ⟩
    #-drop-take m n f g =
               #⟨ (f ∘ drop m) |∧| (g ∘ take m) ⟩
             ≡⟨ ≗-cong-# ((f ∘ drop m) |∧| (g ∘ take m)) ((g ∘ take m) |∧| (f ∘ drop m)) (λ x → Bool°.+-comm (f (drop m x)) _) ⟩
               #⟨ (g ∘ take m) |∧| (f ∘ drop m) ⟩
             ≡⟨ #-take-drop m n g f ⟩
               #⟨ g ⟩ * #⟨ f ⟩
             ≡⟨ ℕ°.*-comm #⟨ g ⟩ _ ⟩
               #⟨ f ⟩ * #⟨ g ⟩
             ∎
      where open ≡-Reasoning

    #-take : ∀ m n (f : Bits m → Bit) → #⟨ f ∘ take m {n} ⟩ ≡ 2^ n * #⟨ f ⟩
    #-take m n f = #⟨ f ∘ take m {n} ⟩
                 ≡⟨ #-drop-take m n (always n) f ⟩
                   #⟨ always n ⟩ * #⟨ f ⟩
                 ≡⟨ cong (flip _*_ #⟨ f ⟩) (#always≡2^ n) ⟩
                   2^ n * #⟨ f ⟩
                 ∎
      where open ≡-Reasoning

    #-drop : ∀ m n (f : Bits m → Bit) → #⟨ f ∘ drop n ⟩ ≡ 2^ n * #⟨ f ⟩
    #-drop m n f = #⟨ f ∘ drop n ⟩
                 ≡⟨ #-take-drop n m (always n) f ⟩
                   #⟨ always n ⟩ * #⟨ f ⟩
                 ≡⟨ cong (flip _*_ #⟨ f ⟩) (#always≡2^ n) ⟩
                   2^ n * #⟨ f ⟩
                 ∎
      where open ≡-Reasoning

    #⟨_==⟩ : ∀ {n} (xs : Bits n) → #⟨ flip _==_ xs ⟩ ≡ 1
    #⟨ xs ==⟩ = trans (≗-cong-# (flip _==_ xs) (_==_ xs) (flip ==-comm xs)) #⟨== xs ⟩

    #⇒ : ∀ {n} (f g : Bits n → Bit) → (∀ x → T (f x) → T (g x)) → #⟨ f ⟩ ≤ #⟨ g ⟩
    #⇒ {zero} f g f⇒g with f [] | g [] | f⇒g []
    ... | true  | true  | _ = s≤s z≤n
    ... | true  | false | p = ⊥-elim (p _)
    ... | false | _     | _ = z≤n
    #⇒ {suc n} f g f⇒g = #⇒ (f ∘ 0∷_) (g ∘ 0∷_) (f⇒g ∘ 0∷_)
                    +-mono #⇒ (f ∘ 1∷_) (g ∘ 1∷_) (f⇒g ∘ 1∷_)

    #-∧-∨ᵇ : ∀ x y → Bool.toℕ (x ∧ y) + Bool.toℕ (x ∨ y) ≡ Bool.toℕ x + Bool.toℕ y
    #-∧-∨ᵇ true y rewrite ℕ°.+-comm (Bool.toℕ y) 1 = refl
    #-∧-∨ᵇ false y = refl

    #-lem : ∀ {n} → (f g : Bits n → Bit) → #⟨ f ⟩ ≡ #⟨ g |∧| f ⟩ + #⟨ |not| g |∧| f ⟩
    #-lem {zero} f g with g []
    ... | 0b = refl
    ... | 1b = ℕ°.+-comm 0 #⟨ f ⟩
    #-lem {suc n} f g 
      rewrite #-lem (f ∘ 0∷_) (g ∘ 0∷_)
            | #-lem (f ∘ 1∷_) (g ∘ 1∷_)
            = +-interchange #⟨ (g ∘ 0∷_) |∧| (f ∘ 0∷_) ⟩
                #⟨ |not| (g ∘ 0∷_) |∧| (f ∘ 0∷_) ⟩ 
                #⟨ (g ∘ 1∷_) |∧| (f ∘ 1∷_) ⟩
                #⟨ |not| (g ∘ 1∷_) |∧| (f ∘ 1∷_) ⟩


    #-∧-snd : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∧| g ⟩ ≤ #⟨ g ⟩
    #-∧-snd {zero} f g with f [] | g []
    ... | 0b | 0b = z≤n
    ... | 0b | 1b = z≤n
    ... | 1b | _ = ℕ≤.reflexive refl
    #-∧-snd {suc n} f g = #-∧-snd (f ∘ 0∷_) (g ∘ 0∷_) 
                   +-mono #-∧-snd (f ∘ 1∷_) (g ∘ 1∷_)

    #-∧-fst : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∧| g ⟩ ≤ #⟨ f ⟩
    #-∧-fst f g = 
              #⟨ f |∧| g ⟩ 
            ≡⟨ #-≗ (f |∧| g) (g |∧| f) (|∧|-comm f g) ⟩ 
              #⟨ g |∧| f ⟩ 
            ≤⟨ #-∧-snd g f ⟩ 
              #⟨ f ⟩ ∎
      where open ≤-Reasoning

    #-∧-∨ : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∧| g ⟩ + #⟨ f |∨| g ⟩ ≡ #⟨ f ⟩ + #⟨ g ⟩
    #-∧-∨ {zero} f g = #-∧-∨ᵇ (f []) (g [])
    #-∧-∨ {suc n} f g =
      trans
        (trans
           (helper #⟨ (f ∘ 0∷_) |∧| (g ∘ 0∷_) ⟩
                   #⟨ (f ∘ 1∷_) |∧| (g ∘ 1∷_) ⟩
                   #⟨ (f ∘ 0∷_) |∨| (g ∘ 0∷_) ⟩
                   #⟨ (f ∘ 1∷_) |∨| (g ∘ 1∷_) ⟩)
           (cong₂ _+_ (#-∧-∨ (f ∘ 0∷_) (g ∘ 0∷_))
                      (#-∧-∨ (f ∘ 1∷_) (g ∘ 1∷_))))
        (helper #⟨ f ∘ 0∷_ ⟩ #⟨ g ∘ 0∷_ ⟩ #⟨ f ∘ 1∷_ ⟩ #⟨ g ∘ 1∷_ ⟩)
        where open SemiringSolver
              helper : ∀ x y z t → x + y + (z + t) ≡ x + z + (y + t)
              helper = solve 4 (λ x y z t → x :+ y :+ (z :+ t) := x :+ z :+ (y :+ t)) refl

    #∨' : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∨| g ⟩ ≤ #⟨ f ⟩ + #⟨ g ⟩
    #∨' {zero} f g with f []
    ... | true  = s≤s z≤n
    ... | false = ℕ≤.refl
    #∨' {suc _} f g = ℕ≤.trans (#∨' (f ∘ 0∷_) (g ∘ 0∷_) +-mono
                                 #∨' (f ∘ 1∷_) (g ∘ 1∷_))
                        (ℕ≤.reflexive
                          (helper #⟨ f ∘ 0∷_ ⟩ #⟨ g ∘ 0∷_ ⟩ #⟨ f ∘ 1∷_ ⟩ #⟨ g ∘ 1∷_ ⟩))
        where open SemiringSolver
              helper : ∀ x y z t → x + y + (z + t) ≡ x + z + (y + t)
              helper = solve 4 (λ x y z t → x :+ y :+ (z :+ t) := x :+ z :+ (y :+ t)) refl

    #∨ : ∀ {m n o} {f g : Bits o → Bit} → #⟨ f ⟩ ≤ m → #⟨ g ⟩ ≤ n → #⟨ (λ x → f x ∨ g x) ⟩ ≤ (m + n)
    #∨ {m} {n} {o} {f} {g} pf pg = ℕ≤.trans (#∨' f g) (pf +-mono pg)

    #∧ : ∀ {m n o} {f g : Bits o → Bit} → #⟨ f ⟩ ≤ m → #⟨ g ⟩ ≤ n → #⟨ f |∧| g ⟩ ≤ (m + n)
    #∧ {f = f} {g} pf pg = ℕ≤.trans (#⇒ (f |∧| g) (f |∨| g) (λ x → ∧⇒∨ (f x) (g x))) (#∨ {f = f} pf pg)

    #-bound : ∀ c (f : Bits c → Bit) → #⟨ f ⟩ ≤ 2^ c
    #-bound zero    f = Bool.toℕ≤1 (f [])
    #-bound (suc c) f = #-bound c (f ∘ 0∷_) +-mono #-bound c (f ∘ 1∷_)

    #-∘vnot : ∀ c (f : Bits c → Bit) → #⟨ f ⟩ ≡ #⟨ f ∘ vnot ⟩
    #-∘vnot _ f = #-⊕ 1ⁿ f

    #-∘xorᵢ : ∀ {c} (i : Fin c) (f : Bits c → Bit) b → #⟨ f ⟩ ≡ #⟨ f ∘ onᵢ (_xor_ b) i ⟩
    #-∘xorᵢ i f b = pf
      where pad = onᵢ (_xor_ b) i 0ⁿ
            pf : #⟨ f ⟩ ≡ #⟨ f ∘ onᵢ (_xor_ b) i ⟩
            pf rewrite #-⊕ pad f = ≗-cong-# (f ∘ _⊕_ pad) (f ∘ onᵢ (_xor_ b) i) (cong (_$_ f) ∘ sym ∘ onᵢ-xor-⊕ b i)

    #-∘notᵢ : ∀ {c} (i : Fin c) (f : Bits c → Bit) → #⟨ f ⟩ ≡ #⟨ f ∘ notᵢ i ⟩
    #-∘notᵢ i f = #-∘xorᵢ i f true

    #-not∘ : ∀ c (f : Bits c → Bit) → #⟨ f ⟩ ≡ 2^ c ∸ #⟨ not ∘ f ⟩
    #-not∘ zero f with f []
    ... | true  = ≡.refl
    ... | false = ≡.refl
    #-not∘ (suc c) f
      rewrite #-not∘ c (f ∘ 0∷_)
            | #-not∘ c (f ∘ 1∷_) = factor-+-∸ (#-bound c (not ∘ f ∘ 0∷_)) (#-bound c (not ∘ f ∘ 1∷_))

    #-not∘′ : ∀ c (f : Bits c → Bit) → #⟨ not ∘ f ⟩ ≡ 2^ c ∸ #⟨ f ⟩
    #-not∘′ c f = #⟨ not ∘ f ⟩
               ≡⟨ #-not∘ c (not ∘ f) ⟩
                 2^ c ∸ #⟨ not ∘ not ∘ f ⟩
               ≡⟨ ≡.cong (λ g → 2^ c ∸ g) (≗-cong-# (not ∘ not ∘ f) f (not-involutive ∘ f)) ⟩
                 2^ c ∸ #⟨ f ⟩
               ∎
      where open ≡-Reasoning


    difference-lemma : ∀ {n}(A B F : Bits n → Bit) 
      → #⟨ |not| F |∧| A ⟩ ≡ #⟨ |not| F |∧| B ⟩
      → dist #⟨ A ⟩ #⟨ B ⟩ ≤ #⟨ F ⟩
    difference-lemma A B F A∧¬F≡B∧¬F = 
       dist #⟨ A ⟩ #⟨ B ⟩ 
         ≡⟨ cong₂ dist (#-lem A F) (#-lem B F) ⟩
       dist (#⟨ F |∧| A ⟩ + #⟨ |not| F |∧| A ⟩)
            (#⟨ F |∧| B ⟩ + #⟨ |not| F |∧| B ⟩)
         ≡⟨ cong₂ dist (ℕ°.+-comm #⟨ F |∧| A ⟩ #⟨ |not| F |∧| A ⟩) 
                       (ℕ°.+-comm #⟨ F |∧| B ⟩ #⟨ |not| F |∧| B ⟩) ⟩
       dist (#⟨ |not| F |∧| A ⟩ + #⟨ F |∧| A ⟩)
            (#⟨ |not| F |∧| B ⟩ + #⟨ F |∧| B ⟩)
         ≡⟨ cong₂ dist (refl {x = #⟨ |not| F |∧| A ⟩ 
                              + #⟨ F |∧| A ⟩})
                       (cong₂ _+_ (sym A∧¬F≡B∧¬F)
                             (refl {x = #⟨ F |∧| B ⟩})) ⟩
       dist (#⟨ |not| F |∧| A ⟩ + #⟨ F |∧| A ⟩)
            (#⟨ |not| F |∧| A ⟩ + #⟨ F |∧| B ⟩)
         ≡⟨ dist-x+ #⟨ |not| F |∧| A ⟩ #⟨ F |∧| A ⟩ #⟨ F |∧| B ⟩ ⟩
       dist #⟨ F |∧| A ⟩ #⟨ F |∧| B ⟩
         ≤⟨ dist-bounded {#⟨ F |∧| A ⟩} {#⟨ F |∧| B ⟩} {#⟨ F ⟩} 
            (#-∧-fst F A) (#-∧-fst F B) ⟩ 
       #⟨ F ⟩ ∎
     where open ≤-Reasoning

open SimpleSearch public
open Sum public
open Count public

#⟨⟩-spec : ∀ {n} (pred : Bits n → Bool) → #⟨ pred ⟩ ≡ Fin.toℕ #⟨ pred ⟩ᶠ
#⟨⟩-spec {zero}  pred with pred []
... | true = refl
... | false = refl
#⟨⟩-spec {suc n} pred rewrite count-++ pred (vmap 0∷_ (allBits n)) (vmap 1∷_ (allBits n))
                            | #⟨⟩-spec {n} (pred ∘ 0∷_)
                            | #⟨⟩-spec {n} (pred ∘ 1∷_)
                            | count-∘ 0∷_ pred (allBits n)
                            | count-∘ 1∷_ pred (allBits n) = refl

ext-# : ∀ {c} {f g : Bits c → Bit} → f ≗ g → #⟨ f ⟩ᶠ ≡ #⟨ g ⟩ᶠ
ext-# f≗g = ext-countᶠ f≗g (allBits _)

find? : ∀ {n a} {A : Set a} → (Bits n →? A) →? A
find? = search (M?._∣_ _)

findB : ∀ {n} → (Bits n → Bool) →? Bits n
findB pred = find? (λ x → if pred x then just x else nothing)

|de-morgan| : ∀ {n} (f g : Bits n → Bit) → f |∨| g ≗ not ∘ ((not ∘ f) |∧| (not ∘ g))
|de-morgan| f g x with f x
... | true = refl
... | false = sym (not-involutive _)

search-de-morgan : ∀ {n} op (f g : Bits n → Bit) →
                   search op (f |∨| g) ≡ search op (not ∘ ((not ∘ f) |∧| (not ∘ g)))
search-de-morgan op f g = search-≗ op _ _ (|de-morgan| f g)

search-hom :
  ∀ {n a b}
    {A : Set a} {B : Set b}
    (_+_ : A → A → A)
    (_*_ : B → B → B)
    (f : A → B)
    (p : Bits n → A)
    (hom : ∀ x y → f (x + y) ≡ f x * f y)
    → f (search _+_ p) ≡ search _*_ (f ∘ p)
search-hom {zero}  _   _   _ _ _   = refl
search-hom {suc n} _+_ _*_ f p hom =
   trans (hom _ _)
         (cong₂ _*_ (search-hom _+_ _*_ f (p ∘ 0∷_) hom)
                    (search-hom _+_ _*_ f (p ∘ 1∷_) hom))

sucBCarry : ∀ {n} → Bits n → Bits (1 + n)
sucBCarry [] = 0b ∷ []
sucBCarry (0b ∷ xs) = 0b ∷ sucBCarry xs
sucBCarry (1b ∷ xs) with sucBCarry xs
... | 0b ∷ bs = 0b ∷ 1b ∷ bs
... | 1b ∷ bs = 1b ∷ 0b ∷ bs

sucB : ∀ {n} → Bits n → Bits n
sucB = tail ∘ sucBCarry

_[mod_] : ℕ → ℕ → Set
a [mod b ] = DivMod' a b

proj : ∀ {a} {A : Set a} → A × A → Bit → A
proj (x₀ , x₁) 0b = x₀
proj (x₀ , x₁) 1b = x₁

rewire : ∀ {i o} → (Fin o → Fin i) → i →ᵇ o
rewire = V.rewire

rewireTbl : ∀ {i o} → RewireTbl i o → i →ᵇ o
rewireTbl = V.rewireTbl

module ReversedBits where
  sucRB : ∀ {n} → Bits n → Bits n
  sucRB [] = []
  sucRB (0b ∷ xs) = 1b ∷ xs
  sucRB (1b ∷ xs) = 0b ∷ sucRB xs

toFin : ∀ {n} → Bits n → Fin (2^ n)
toFin         []        = zero
toFin         (0b ∷ xs) = inject+ _ (toFin xs)
toFin {suc n} (1b ∷ xs) = raise (2^ n) (toFin xs)

{-
toℕ : ∀ {n} → Bits n → ℕ
toℕ = Fin.toℕ ∘ toFin
-}

toℕ : ∀ {n} → Bits n → ℕ
toℕ         []        = zero
toℕ         (0b ∷ xs) = toℕ xs
toℕ {suc n} (1b ∷ xs) = 2^ n + toℕ xs

toℕ-bound : ∀ {n} (xs : Bits n) → toℕ xs < 2^ n 
toℕ-bound         [] = s≤s z≤n
toℕ-bound {suc n} (1b ∷ xs) rewrite +-assoc-comm 1 (2^ n) (toℕ xs) = ℕ≤.refl {2^ n} +-mono toℕ-bound xs
toℕ-bound {suc n} (0b ∷ xs) = ≤-steps (2^ n) (toℕ-bound xs)

toℕ≤2ⁿ+ : ∀ {n} (x : Bits n) {y} → toℕ {n} x ≤ 2^ n + y
toℕ≤2ⁿ+ {n} x {y} = ℕ≤.trans (≤-steps y (≤-pred (≤-steps 1 (toℕ-bound x))))
                             (ℕ≤.reflexive (ℕ°.+-comm y (2^ n)))

2ⁿ+≰toℕ : ∀ {n x} (y : Bits n) → 2^ n + x ≰ toℕ {n} y
2ⁿ+≰toℕ {n} {x} y p = ¬n+≤y<n (2^ n) p (toℕ-bound y)

toℕ-inj : ∀ {n} (x y : Bits n) → toℕ x ≡ toℕ y → x ≡ y
toℕ-inj         []        []        _ = refl
toℕ-inj         (0b ∷ xs) (0b ∷ ys) p = cong 0∷_ (toℕ-inj xs ys p)
toℕ-inj {suc n} (1b ∷ xs) (1b ∷ ys) p = cong 1∷_ (toℕ-inj xs ys (cancel-+-left (2^ n) p))
toℕ-inj {suc n} (0b ∷ xs) (1b ∷ ys) p = ⊥-elim (2ⁿ+≰toℕ xs (ℕ≤.reflexive (≡.sym p)))
toℕ-inj {suc n} (1b ∷ xs) (0b ∷ ys) p = ⊥-elim (2ⁿ+≰toℕ ys (ℕ≤.reflexive p))

data _≤ᴮ_ : ∀ {n} (p q : Bits n) → Set where
  []    : [] ≤ᴮ []
  there : ∀ {n} {p q : Bits n} b → p ≤ᴮ q → (b ∷ p) ≤ᴮ (b ∷ q)
  0-1   : ∀ {n} (p q : Bits n) → 0∷ p ≤ᴮ 1∷ q

≤ᴮ→<= : ∀ {n} {p q : Bits n} → p ≤ᴮ q → T (p <= q)
≤ᴮ→<= [] = _
≤ᴮ→<= (there 0b pf) = ≤ᴮ→<= pf
≤ᴮ→<= (there 1b pf) = ≤ᴮ→<= pf
≤ᴮ→<= (0-1 p q) = _

<=→≤ᴮ : ∀ {n} (p q : Bits n) → T (p <= q) → p ≤ᴮ q
<=→≤ᴮ [] [] _ = []
<=→≤ᴮ (1b ∷ p) (0b ∷ q) ()
<=→≤ᴮ (0b ∷ p) (1b ∷ q) _  = 0-1 p q
<=→≤ᴮ (0b ∷ p) (0b ∷ q) pf = there 0b (<=→≤ᴮ p q pf)
<=→≤ᴮ (1b ∷ p) (1b ∷ q) pf = there 1b (<=→≤ᴮ p q pf)

toℕ-≤-inj : ∀ {n} (x y : Bits n) → toℕ x ≤ toℕ y → x ≤ᴮ y
toℕ-≤-inj     [] [] p = []
toℕ-≤-inj         (0b ∷ xs) (0b ∷ ys) p = there 0b (toℕ-≤-inj xs ys p)
toℕ-≤-inj         (0b ∷ xs) (1b ∷ ys) p = 0-1 _ _
toℕ-≤-inj {suc n} (1b ∷ xs) (0b ∷ ys) p = ⊥-elim (2ⁿ+≰toℕ ys p)
toℕ-≤-inj {suc n} (1b ∷ xs) (1b ∷ ys) p = there 1b (toℕ-≤-inj xs ys (+-≤-inj (2^ n) p))

fromℕ : ∀ {n} → ℕ → Bits n
fromℕ {zero}  _ = []
fromℕ {suc n} x = if 2^ n ℕ<= x then 1∷ fromℕ (x ∸ 2^ n) else 0∷ fromℕ x

fromℕ′ : ∀ {n} → ℕ → Bits n
fromℕ′ = fold 0ⁿ sucB

fromFin : ∀ {n} → Fin (2^ n) → Bits n
fromFin = fromℕ ∘ Fin.toℕ

lookupTbl : ∀ {n a} {A : Set a} → Bits n → Vec A (2^ n) → A
lookupTbl         []         (x ∷ []) = x
lookupTbl         (0b ∷ key) tbl      = lookupTbl key (take _ tbl)
lookupTbl {suc n} (1b ∷ key) tbl      = lookupTbl key (drop (2^ n) tbl)

funFromTbl : ∀ {n a} {A : Set a} → Vec A (2^ n) → (Bits n → A)
funFromTbl = flip lookupTbl

tblFromFun : ∀ {n a} {A : Set a} → (Bits n → A) → Vec A (2^ n)
-- tblFromFun f = tabulate (f ∘ fromFin)
tblFromFun {zero} f = f [] ∷ []
tblFromFun {suc n} f = tblFromFun {n} (f ∘ 0∷_) ++ tblFromFun {n} (f ∘ 1∷_)

funFromTbl∘tblFromFun : ∀ {n a} {A : Set a} (fun : Bits n → A) → funFromTbl (tblFromFun fun) ≗ fun
funFromTbl∘tblFromFun {zero} f [] = refl
funFromTbl∘tblFromFun {suc n} f (0b ∷ xs)
  rewrite take-++ (2^ n) (tblFromFun {n} (f ∘ 0∷_)) (tblFromFun {n} (f ∘ 1∷_)) =
    funFromTbl∘tblFromFun {n} (f ∘ 0∷_) xs
funFromTbl∘tblFromFun {suc n} f (1b ∷ xs)
  rewrite drop-++ (2^ n) (tblFromFun {n} (f ∘ 0∷_)) (tblFromFun {n} (f ∘ 1∷_))
        | take-++ (2^ n) (tblFromFun {n} (f ∘ 1∷_)) [] =
    funFromTbl∘tblFromFun {n} (f ∘ 1∷_) xs

tblFromFun∘funFromTbl : ∀ {n a} {A : Set a} (tbl : Vec A (2^ n)) → tblFromFun {n} (funFromTbl tbl) ≡ tbl
tblFromFun∘funFromTbl {zero} (x ∷ []) = refl
tblFromFun∘funFromTbl {suc n} tbl
  rewrite tblFromFun∘funFromTbl {n} (take _ tbl)
        | tblFromFun∘funFromTbl {n} (drop (2^ n) tbl)
        = take-drop-lem (2^ n) tbl

{-
sucB-lem : ∀ {n} x → toℕ {2^ n} (sucB x) [mod 2 ^ n ] ≡ (suc (toℕ x)) [mod 2 ^ n ]
sucB-lem x = {!!}

-- _ᴮ : (s : String) {pf : IsBitString s} → Bits (length s)
-- _ᴮ =
-}

2ⁿ≰toℕ : ∀ {n} (xs : Bits n) → 2^ n ≰ toℕ xs
2ⁿ≰toℕ xs p = ¬n≤x<n _ p (toℕ-bound xs)

Tnot2ⁿ<=toℕ : ∀ {n} (xs : Bits n) → T (not (2^ n ℕ<= (toℕ xs)))
Tnot2ⁿ<=toℕ {n} xs with (2^ n) ℕ<= (toℕ xs) | ≡.inspect (_ℕ<=_ (2^ n)) (toℕ xs)
... | true  | ≡.[ p ] = 2ⁿ≰toℕ xs (<=.sound (2^ n) (toℕ xs) (≡→T p))
... | false |     _   = _

fromℕ∘toℕ : ∀ {n} (x : Bits n) → fromℕ (toℕ x) ≡ x
fromℕ∘toℕ [] = ≡.refl
fromℕ∘toℕ {suc n} (true ∷ xs)
  rewrite T→≡ (<=-steps′ {2^ n} (toℕ xs))
        | ℕ°.+-comm (2^ n) (toℕ xs)
        | m+n∸n≡m (toℕ xs) (2^ n)
        | fromℕ∘toℕ xs
        = ≡.refl
fromℕ∘toℕ (false ∷ xs)
  rewrite Tnot→≡ (Tnot2ⁿ<=toℕ xs)
        | fromℕ∘toℕ xs
        = ≡.refl

toℕ∘fromℕ : ∀ {n} x → x < 2^ n → toℕ {n} (fromℕ x) ≡ x
toℕ∘fromℕ {zero} .0 (s≤s z≤n) = ≡.refl
toℕ∘fromℕ {suc n} x x<2ⁿ with 2^ n ℕ<= x | ≡.inspect (_ℕ<=_ (2^ n)) x
... | true  | ≡.[ p ] rewrite toℕ∘fromℕ {n} (x ∸ 2^ n) (x<2y→x∸y<y x (2^ n) x<2ⁿ) = m+n∸m≡n {2^ n} {x} (<=.sound (2^ n) x (≡→T p))
... | false | ≡.[ p ] = toℕ∘fromℕ {n} x (<=.sound (suc x) (2^ n) (not<=→< (2^ n) x (≡→Tnot p)))

fromℕ-inj : ∀ {n} {x y : ℕ} → x < 2^ n → y < 2^ n → fromℕ {n} x ≡ fromℕ y → x ≡ y
fromℕ-inj {n} {x} {y} x< y< fx≡fy
  = x
  ≡⟨ ≡.sym (toℕ∘fromℕ {n} x x<) ⟩
    toℕ (fromℕ {n} x)
  ≡⟨ ≡.cong toℕ fx≡fy ⟩
    toℕ (fromℕ {n} y)
  ≡⟨ toℕ∘fromℕ {n} y y< ⟩
    y
  ∎ where open ≡-Reasoning

open Defs public
