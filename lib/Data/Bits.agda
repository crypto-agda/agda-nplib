{-# OPTIONS --without-K #-}
module Data.Bits where

open import Algebra
open import Level.NP
open import Type hiding (★)
open import Data.Nat.NP hiding (_==_) renaming (_<=_ to _ℕ<=_)
open import Data.Bit using (Bit)
open import Data.Two renaming (_==_ to _==ᵇ_)
open import Data.Fin.NP using (Fin; zero; suc; inject₁; inject+; raise; Fin▹ℕ)
open import Data.Vec.NP
open import Function.NP
import Data.List.NP as L

-- Re-export some vector functions, maybe they should be given
-- less generic types.
open Data.Vec.NP public using ([]; _∷_; _++_; head; tail; map; replicate; RewireTbl; rewire; rewireTbl; onᵢ)

Bits : ℕ → ★₀
Bits = Vec Bit

_→ᵇ_ : ℕ → ℕ → ★₀
i →ᵇ o = Bits i → Bits o

0ⁿ : ∀ {n} → Bits n
0ⁿ = replicate 0₂

-- Notice that all empty vectors are the same, hence 0ⁿ {0} ≡ 1ⁿ {0}
1ⁿ : ∀ {n} → Bits n
1ⁿ = replicate 1₂

0∷_ : ∀ {n} → Bits n → Bits (suc n)
0∷ xs = 0₂ ∷ xs

-- can't we make these pattern aliases?
1∷_ : ∀ {n} → Bits n → Bits (suc n)
1∷ xs = 1₂ ∷ xs

_!_ : ∀ {a n} {A : ★ a} → Vec A n → Fin n → A
_!_ = flip lookup

-- see Data.Bits.Properties
_==_ : ∀ {n} (bs₀ bs₁ : Bits n) → Bit
[]         == []         = 1₂
(b₀ ∷ bs₀) == (b₁ ∷ bs₁) = (b₀ ==ᵇ b₁) ∧ bs₀ == bs₁

_<=_ : ∀ {n} (xs ys : Bits n) → Bit
[]        <= []        = 1₂
(1₂ ∷ xs) <= (0₂ ∷ ys) = 0₂
(0₂ ∷ xs) <= (1₂ ∷ ys) = 1₂
(_  ∷ xs) <= (_  ∷ ys) = xs <= ys

infixr 5 _⊕_
_⊕_ : ∀ {n} (bs₀ bs₁ : Bits n) → Bits n
_⊕_ = zipWith _xor_

⊕-group : ℕ → Group ₀ ₀
⊕-group = LiftGroup.group Xor°.+-group

module ⊕-Group  (n : ℕ) = Group (⊕-group n)
module ⊕-Monoid (n : ℕ) = Monoid (⊕-Group.monoid n)

-- Negate all bits, i.e. "xor"ing them by one.
vnot : ∀ {n} → Endo (Bits n)
vnot = _⊕_ 1ⁿ

-- Negate the i-th bit.
notᵢ : ∀ {n} (i : Fin n) → Bits n → Bits n
notᵢ = onᵢ not

msb : ∀ k {n} → Bits (k + n) → Bits k
msb = take

lsb : ∀ k {n} → Bits (n + k) → Bits k
lsb _ {n} = drop n

msb₂ : ∀ {n} → Bits (2 + n) → Bits 2
msb₂ = msb 2

lsb₂ : ∀ {n} → Bits (2 + n) → Bits 2
lsb₂ = reverse ∘ msb 2 ∘ reverse

#1 : ∀ {n} → Bits n → Fin (suc n)
#1 [] = zero
#1 (0₂ ∷ bs) = inject₁ (#1 bs)
#1 (1₂ ∷ bs) = suc (#1 bs)

#0 : ∀ {n} → Bits n → Fin (suc n)
#0 = #1 ∘ map not

allBitsL : ∀ n → L.List (Bits n)
allBitsL _ = replicateM (toList (0₂ ∷ 1₂ ∷ []))
  where open L.Monad

allBits : ∀ n → Vec (Bits n) (2^ n)
allBits zero    = [] ∷ []
allBits (suc n) = map 0∷_ bs ++ map 1∷_ bs
  where bs = allBits n

always : ∀ n → Bits n → Bit
always _ _ = 1₂

never  : ∀ n → Bits n → Bit
never _ _ = 0₂

_∨°_ : ∀ {n} → (f g : Bits n → Bit) → Bits n → Bit
_∨°_ f g x = f x ∨ g x

_∧°_ : ∀ {n} → (f g : Bits n → Bit) → Bits n → Bit
_∧°_ f g x = f x ∧ g x

not° : ∀ {n} (f : Bits n → Bit) → Bits n → Bit
not° f = not ∘ f

view∷ : ∀ {n a b} {A : ★ a} {B : ★ b} → (A → Vec A n → B) → Vec A (suc n) → B
view∷ f (x ∷ xs) = f x xs

sucBCarry : ∀ {n} → Bits n → Bits (1 + n)
sucBCarry []        = 0₂ ∷ []
sucBCarry (0₂ ∷ xs) = 0₂ ∷ sucBCarry xs
sucBCarry (1₂ ∷ xs) = view∷ (λ x xs → x ∷ not x ∷ xs) (sucBCarry xs)

sucB : ∀ {n} → Bits n → Bits n
sucB = tail ∘ sucBCarry

--_[mod_] : ℕ → ℕ → ★₀
--a [mod b ] = DivMod' a b

module ReversedBits where
  sucRB : ∀ {n} → Bits n → Bits n
  sucRB [] = []
  sucRB (0₂ ∷ xs) = 1₂ ∷ xs
  sucRB (1₂ ∷ xs) = 0₂ ∷ sucRB xs

toFin : ∀ {n} → Bits n → Fin (2^ n)
toFin         []        = zero
toFin         (0₂ ∷ xs) = inject+ _ (toFin xs)
toFin {suc n} (1₂ ∷ xs) = raise (2^ n) (toFin xs)

Bits▹ℕ : ∀ {n} → Bits n → ℕ
Bits▹ℕ         []        = zero
Bits▹ℕ         (0₂ ∷ xs) = Bits▹ℕ xs
Bits▹ℕ {suc n} (1₂ ∷ xs) = 2^ n + Bits▹ℕ xs

ℕ▹Bits : ∀ {n} → ℕ → Bits n
ℕ▹Bits {zero}  _ = []
ℕ▹Bits {suc n} x = [0: 0∷ ℕ▹Bits x
                    1: 1∷ ℕ▹Bits (x ∸ 2^ n)
                   ]′ (2^ n ℕ<= x)

ℕ▹Bits′ : ∀ {n} → ℕ → Bits n
ℕ▹Bits′ = fold 0ⁿ sucB

fromFin : ∀ {n} → Fin (2^ n) → Bits n
fromFin = ℕ▹Bits ∘ Fin▹ℕ

lookupTbl : ∀ {n a} {A : ★ a} → Bits n → Vec A (2^ n) → A
lookupTbl         []         (x ∷ []) = x
lookupTbl         (0₂ ∷ key) tbl      = lookupTbl key (take _ tbl)
lookupTbl {suc n} (1₂ ∷ key) tbl      = lookupTbl key (drop (2^ n) tbl)

funFromTbl : ∀ {n a} {A : ★ a} → Vec A (2^ n) → (Bits n → A)
funFromTbl = flip lookupTbl

tblFromFun : ∀ {n a} {A : ★ a} → (Bits n → A) → Vec A (2^ n)
-- tblFromFun f = tabulate (f ∘ fromFin)
tblFromFun {zero}  f = f [] ∷ []
tblFromFun {suc n} f = tblFromFun {n} (f ∘ 0∷_) ++ tblFromFun {n} (f ∘ 1∷_)
