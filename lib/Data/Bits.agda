module Data.Bits where

-- cleanup
open import Category.Applicative
open import Category.Monad
open import Data.Nat.NP hiding (_≤_; _==_)
open import Data.Nat.DivMod
open import Data.Bool.NP hiding (_==_)
open import Data.Maybe
import Data.Fin as Fin
open Fin using (Fin; zero; suc; #_; inject₁; inject+; raise)
open import Data.Vec.NP hiding (_⊛_) renaming (map to vmap)
open import Data.Vec.N-ary.NP
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; uncurry; proj₁; proj₂)
open import Function.NP hiding (_→⟨_⟩_)
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡
open import Algebra.FunctionProperties
import Data.List as L

open import Data.Bool.NP public using (_xor_)
open import Data.Vec.NP public using ([]; _∷_; head; tail; replicate)

Bit : Set
Bit = Bool

pattern 0b = false
pattern 1b = true

Bits : ℕ → Set
Bits = Vec Bit

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

infixr 5 _⊕_
_⊕_ : ∀ {n} (bs₀ bs₁ : Bits n) → Bits n
_⊕_ = zipWith _xor_

vnot : ∀ {n} → Endo (Bits n)
vnot = _⊕_ 1ⁿ

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

private
 module M {a} {A : Set a} {M} (appl : RawApplicative M) where
  open RawApplicative appl

  replicateM : ∀ {n} → M A → M (Vec A n)
  replicateM {n = zero}  _ = pure []
  replicateM {n = suc n} x = pure _∷_ ⊛ x ⊛ replicateM x

open M public

allBitsL : ∀ n → L.List (Bits n)
allBitsL _ = replicateM rawIApplicative (toList (0b ∷ 1b ∷ []))

  where open RawMonad L.monad
allBits : ∀ n → Vec (Bits n) (2 ^ n)
allBits zero = [] ∷ []
allBits (suc n) rewrite ℕ°.+-comm (2 ^ n) 0 = vmap 0∷_ bs ++ vmap 1∷_ bs
  where bs = allBits n

#⟨_⟩ : ∀ {n} → (Bits n → Bool) → Fin (suc (2 ^ n))
#⟨ pred ⟩ = count pred (allBits _)

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

module ReversedBits where
  sucRB : ∀ {n} → Bits n → Bits n
  sucRB [] = []
  sucRB (0b ∷ xs) = 1b ∷ xs
  sucRB (1b ∷ xs) = 0b ∷ sucRB xs

toFin : ∀ {n} → Bits n → Fin (2 ^ n)
toFin         []        = zero
toFin         (0b ∷ xs) = inject+ _ (toFin xs)
toFin {suc n} (1b ∷ xs) = raise (2 ^ n) (inject+ 0 (toFin xs))

{-
toℕ : ∀ {n} → Bits n → ℕ
toℕ = Fin.toℕ ∘ toFin
-}

toℕ : ∀ {n} → Bits n → ℕ
toℕ         []        = zero
toℕ         (0b ∷ xs) = toℕ xs
toℕ {suc n} (1b ∷ xs) = 2 ^ n + toℕ xs

fromℕ : ∀ {n} → ℕ → Bits n
fromℕ = fold 0ⁿ sucB

fromFin : ∀ {n} → Fin (2 ^ n) → Bits n
fromFin = fromℕ ∘ Fin.toℕ

lookupTbl : ∀ {n a} {A : Set a} → Bits n → Vec A (2 ^ n) → A
lookupTbl         []         (x ∷ []) = x
lookupTbl         (0b ∷ key) tbl      = lookupTbl key (take _ tbl)
lookupTbl {suc n} (1b ∷ key) tbl      = lookupTbl key (take (2 ^ n) (drop (2 ^ n) tbl))

funFromTbl : ∀ {n a} {A : Set a} → Vec A (2 ^ n) → (Bits n → A)
funFromTbl = flip lookupTbl

tblFromFun : ∀ {n a} {A : Set a} → (Bits n → A) → Vec A (2 ^ n)
-- tblFromFun f = tabulate (f ∘ fromFin)
tblFromFun {zero} f = f [] ∷ []
tblFromFun {suc n} f = tblFromFun {n} (f ∘ 0∷_) ++ tblFromFun {n} (f ∘ 1∷_) ++ []

funFromTbl∘tblFromFun : ∀ {n a} {A : Set a} (fun : Bits n → A) → funFromTbl (tblFromFun fun) ≗ fun
funFromTbl∘tblFromFun {zero} f [] = refl
funFromTbl∘tblFromFun {suc n} f (0b ∷ xs)
  rewrite take-++ (2 ^ n) (tblFromFun {n} (f ∘ 0∷_)) (tblFromFun {n} (f ∘ 1∷_) ++ []) =
    funFromTbl∘tblFromFun {n} (f ∘ 0∷_) xs
funFromTbl∘tblFromFun {suc n} f (1b ∷ xs)
  rewrite drop-++ (2 ^ n) (tblFromFun {n} (f ∘ 0∷_)) (tblFromFun {n} (f ∘ 1∷_) ++ [])
        | take-++ (2 ^ n) (tblFromFun {n} (f ∘ 1∷_)) [] =
    funFromTbl∘tblFromFun {n} (f ∘ 1∷_) xs

tblFromFun∘funFromTbl : ∀ {n a} {A : Set a} (tbl : Vec A (2 ^ n)) → tblFromFun {n} (funFromTbl tbl) ≡ tbl
tblFromFun∘funFromTbl {zero} (x ∷ []) = refl
tblFromFun∘funFromTbl {suc n} tbl
  rewrite tblFromFun∘funFromTbl {n} (take _ tbl)
        | tblFromFun∘funFromTbl {n} (take (2 ^ n) (drop (2 ^ n) tbl))
        | take-them-all (2 ^ n) (drop (2 ^ n) tbl)
        | take-drop-lem (2 ^ n) tbl
   = refl

{-
sucB-lem : ∀ {n} x → toℕ {2 ^ n} (sucB x) [mod 2 ^ n ] ≡ (suc (toℕ x)) [mod 2 ^ n ]
sucB-lem x = {!!}

-- sucB-lem : ∀ {n} x → (sucB (fromℕ x)) [mod 2 ^ n ] ≡ fromℕ ((suc x) [mod 2 ^ n ])

toℕ∘fromℕ : ∀ {n} x → toℕ (fromℕ {n} x) ≡ x
toℕ∘fromℕ zero = {!!}
toℕ∘fromℕ (suc x) = {!toℕ∘fromℕ x!}

toℕ∘fromFin : ∀ {n} (x : Fin (2 ^ n)) → toℕ (fromFin x) ≡ Fin.toℕ x
toℕ∘fromFin x = {!!}

toFin∘fromFin : ∀ {n} (x : Fin (2 ^ n)) → toFin (fromFin x) ≡ x
toFin∘fromFin x = {!!}

-- _ᴮ : (s : String) {pf : IsBitString s} → Bits (length s)
-- _ᴮ =
-}
