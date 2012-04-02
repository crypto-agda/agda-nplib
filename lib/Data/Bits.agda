module Data.Bits where

-- cleanup
open import Category.Applicative
open import Category.Monad
open import Data.Nat.NP hiding (_≤_; _==_)
open import Data.Bool
open import Data.Fin using (Fin; zero; suc; toℕ; #_; inject₁)
open import Data.Vec hiding (_⊛_) renaming (map to vmap)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; uncurry)
open import Function.NP hiding (_→⟨_⟩_)
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties
import Data.List as L

Bit : Set
Bit = Bool

pattern 0b = false
pattern 1b = true
{-
data Bit : Set where
  0b 1b : Bit
-}

Bits : ℕ → Set
Bits = Vec Bit

0… : ∀ {n} → Bits n
0… = replicate 0b

-- Warning: 0… {0} ≡ 1… {0}
1… : ∀ {n} → Bits n
1… = replicate 1b

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
vnot = _⊕_ 1…

postulate
  ⊕-assoc : ∀ {n} → Associative _≡_ (_⊕_ {n})
  ⊕-comm  : ∀ {n} → Commutative _≡_ (_⊕_ {n})
  ⊕-left-identity : ∀ {n} → LeftIdentity _≡_ (replicate 0b) (_⊕_ {n})
  ⊕-right-identity : ∀ {n} → RightIdentity _≡_ (replicate 0b) (_⊕_ {n})
  ⊕-≡ : ∀ {n} (x : Bits n) → x ⊕ x ≡ replicate 0b

  ⊕-≢ : ∀ {n} (x : Bits n) → x ⊕ vnot x ≡ replicate 1b
  -- x ⊕ vnot x ≡ x ⊕ (1… ⊕ x) ≡ (x ⊕ x) ⊕ 1… ≡ 0… ⊕ 1… ≡ 1…

msb : ∀ {n} k → Bits (k + n) → Bits k
msb zero    bs       = []
msb (suc k) (b ∷ bs) = b ∷ msb k bs

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

-- _ᴮ : (s : String) {pf : IsBitString s} → Bits (length s)
-- _ᴮ =

11ᵇ : Bits 2
11ᵇ = 1b ∷ 1b ∷ []

private
 module M {a} {A : Set a} {M} (appl : RawApplicative M) where
  open RawApplicative appl

  replicateM : ∀ {n} → M A → M (Vec A n)
  replicateM {n = zero}  _ = pure []
  replicateM {n = suc n} x = pure _∷_ ⊛ x ⊛ replicateM x

open M public

bits⁴ : Vec (Bits 4) 16
bits⁴ = fromList $ replicateM rawIApplicative (toList (0b ∷ 1b ∷ []))
  where open RawMonad L.monad

0000b = bits⁴ ! # 0
0001b = bits⁴ ! # 1
0010b = bits⁴ ! # 2
0011b = bits⁴ ! # 3
0100b = bits⁴ ! # 4
0101b = bits⁴ ! # 5
0110b = bits⁴ ! # 6
0111b = bits⁴ ! # 7
1000b = bits⁴ ! # 8
1001b = bits⁴ ! # 9
1010b = bits⁴ ! # 10
1011b = bits⁴ ! # 11
1100b = bits⁴ ! # 12
1101b = bits⁴ ! # 13
1110b = bits⁴ ! # 14
1111b = bits⁴ ! # 15

η : ∀ {n a} {A : Set a} → Vec A n → Vec A n
η = tabulate ∘ flip lookup
{- alternative
η {zero} = λ _ → []
η {suc n} = λ xs → head xs ∷ η (tail xs)
-}
