module Data.Fin.NP where

open import Function
open import Data.Fin public
open import Data.Nat.NP using (ℕ; zero; suc; _<=_; module ℕ°) renaming (_+_ to _+ℕ_)
open import Data.Bool
open import Data.Sum as Sum

_+′_ : ∀ {m n} (x : Fin m) (y : Fin n) → Fin (m +ℕ n)
_+′_ {suc m} {n} zero y rewrite ℕ°.+-comm (suc m) n = inject+ _ y
suc x +′ y = suc (x +′ y)

_==_ : ∀ {n} (x y : Fin n) → Bool
x == y = helper (compare x y) where
  helper : ∀ {n} {i j : Fin n} → Ordering i j → Bool
  helper (equal _) = true
  helper _         = false

swap : ∀ {i} (x y : Fin i) → Fin i → Fin i
swap x y z = if x == z then y else if y == z then x else z

data FinSum m n : Fin (m +ℕ n) → Set where
  bound : (x : Fin m) → FinSum m n (inject+ n x)
  free  : (x : Fin n) → FinSum m n (raise m x)

open import Relation.Binary.PropositionalEquality

cmp : ∀ m n (x : Fin (m +ℕ n)) → FinSum m n x
cmp zero n x = free x
cmp (suc m) n zero = bound zero
cmp (suc m) n (suc x) with cmp m n x
cmp (suc m) n (suc .(inject+ n x)) | bound x = bound (suc x)
cmp (suc m) n (suc .(raise m x))   | free x  = free x

-- reverse x = n ∸ (1 + x)
reverse : ∀ {n} → Fin n → Fin n
reverse zero    = fromℕ _
reverse (suc x) = inject₁ (reverse x)

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin.Props renaming (reverse to reverse-old)

reverse-fromℕ : ∀ n → reverse (fromℕ n) ≡ zero
reverse-fromℕ zero = refl
reverse-fromℕ (suc n) rewrite reverse-fromℕ n = refl

reverse-inject₁ : ∀ {n} (x : Fin n) → reverse (inject₁ x) ≡ suc (reverse x)
reverse-inject₁ zero = refl
reverse-inject₁ (suc x) rewrite reverse-inject₁ x = refl

reverse-involutive : ∀ {n} (x : Fin n) → reverse (reverse x) ≡ x
reverse-involutive zero = reverse-fromℕ _
reverse-involutive (suc x) rewrite reverse-inject₁ (reverse x) | reverse-involutive x = refl

reverse-lem : ∀ {n} (x : Fin n) → toℕ (reverse x) ≡ n ∸ suc (toℕ x)
reverse-lem zero = to-from _
reverse-lem (suc x) rewrite inject₁-lemma (reverse x) = reverse-lem x

toℕ-ℕ-lem : ∀ {n} (x : Fin (suc n)) → toℕ (n ℕ- x) ≡ n ∸ toℕ x
toℕ-ℕ-lem zero = to-from _
toℕ-ℕ-lem {zero} (suc ())
toℕ-ℕ-lem {suc n} (suc x) = toℕ-ℕ-lem x

reverse-old-lem : ∀ {n} (x : Fin n) → toℕ (reverse-old x) ≡ n ∸ suc (toℕ x)
reverse-old-lem {zero} ()
reverse-old-lem {suc n} x rewrite inject≤-lemma (n ℕ- x) (n∸m≤n (toℕ x) (suc n)) = toℕ-ℕ-lem x
