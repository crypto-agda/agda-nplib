open import Type
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Nat renaming (_*_ to _*ℕ_; _+_ to _+ℕ_)

module Data.Nat.Positive where

data ℕ⁺ : ★ where
  suc : ℕ → ℕ⁺

one : ℕ⁺
one = suc zero

Positive? : ℕ → ★
Positive? zero    = ⊥
Positive? (suc _) = ⊤

[_] : (n : ℕ) {pf : Positive? n} → ℕ⁺
[ suc n ] = suc n
[ zero  ] {()}

_+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
suc x + suc y = suc (suc (x +ℕ y))

_*_ : ℕ⁺ → ℕ⁺ → ℕ⁺
suc x * suc y = suc (x +ℕ y +ℕ x *ℕ y)
