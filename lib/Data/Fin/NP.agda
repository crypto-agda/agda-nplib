module Data.Fin.NP where

open import Function
open import Data.Empty
open import Data.Fin public
open import Data.Nat.NP using (ℕ; zero; suc; _<=_; module ℕ°) renaming (_+_ to _+ℕ_)
open import Data.Bool
import Data.Vec.NP as Vec
open Vec using (Vec; []; _∷_; _∷ʳ_; allFin; lookup; rot₁) renaming (map to vmap)
import Data.Vec.Properties as Vec
open import Data.Maybe.NP
open import Data.Sum as Sum
open import Relation.Binary.PropositionalEquality as ≡

suc-injective : ∀ {m}{i j : Fin m} → Fin.suc i ≡ suc j → i ≡ j
suc-injective refl = refl

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

max : ∀ n → Fin (suc n)
max = fromℕ

-- reverse x = n ∸ (1 + x)
reverse : ∀ {n} → Fin n → Fin n
reverse {suc n} zero    = fromℕ n
reverse {suc n} (suc x) = inject₁ (reverse {n} x)

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

data FinView {n} : Fin (suc n) → Set where
  `fromℕ   : FinView (fromℕ n)
  `inject₁ : ∀ x → FinView (inject₁ x)

sucFinView : ∀ {n} {i : Fin (suc n)} → FinView i → FinView (suc i)
sucFinView `fromℕ = `fromℕ
sucFinView (`inject₁ x) = `inject₁ (suc x)

finView : ∀ {n} → (i : Fin (suc n)) → FinView i
finView {zero}  zero    = `fromℕ
finView {suc n} zero    = `inject₁ zero
finView {suc n} (suc i) = sucFinView (finView i)
finView {zero}  (suc ())

module Modulo where
  modq : ∀ {q} → Fin (suc q) → Maybe (Fin q)
  modq {zero}  _       = nothing
  modq {suc q} zero    = just zero
  modq {suc q} (suc x) = map? suc (modq x)

  modq-inj : ∀ {q} (i j : Fin (suc q)) → modq i ≡ modq j → i ≡ j
  modq-inj {zero} zero zero eq = refl
  modq-inj {zero} zero (suc ()) eq
  modq-inj {zero} (suc ()) zero eq
  modq-inj {zero} (suc ()) (suc ()) eq
  modq-inj {suc q} zero zero eq = refl
  modq-inj {suc q} zero (suc j) eq with modq j
  modq-inj {suc q} zero (suc j) () | nothing
  modq-inj {suc q} zero (suc j) () | just j'
  modq-inj {suc q} (suc i) zero eq with modq i
  modq-inj {suc q} (suc i) zero () | just x
  modq-inj {suc q} (suc i) zero () | nothing
  modq-inj {suc q} (suc i) (suc j) eq with modq i | modq j | modq-inj i j
  modq-inj {suc q} (suc i) (suc j) eq | just x | just x₁ | p = cong suc (p (cong just (suc-injective (just-injective eq))))
  modq-inj {suc q} (suc i) (suc j) () | just x | nothing | p
  modq-inj {suc q} (suc i) (suc j) () | nothing | just x | p
  modq-inj {suc q} (suc i) (suc j) eq | nothing | nothing | p = cong suc (p refl)

  modq′ : ∀ {q} → Fin (suc q) → Fin (suc q)
  modq′ {zero}  _       = zero
  modq′ {suc q} zero    = suc zero
  modq′ {suc q} (suc x) = lift 1 suc (modq′ x)

  modqq : ∀ {q} → Fin q → Fin q
  modqq {zero}  x = x
  modqq {suc q} x = modq′ x

  -- Maybe (Fin n) ≅ Fin (suc n)

  modq′′ : ∀ {q} → Fin (suc q) → Maybe (Fin q)
  modq′′ x with modq′ x
  ... | zero  = nothing
  ... | suc y = just y

  zero∃ : ∀ {q} → Fin q → Fin q
  zero∃ {zero}  ()
  zero∃ {suc q} _  = zero

  sucmod : ∀ {q} → Fin q → Fin q
  sucmod x with modq (suc x)
  ... | nothing = zero∃ x
  ... | just y  = y

  modq-suc : ∀ {q} (i j : Fin q) → modq (suc i) ≢ just (zero∃ j)
  modq-suc {zero} () () eq
  modq-suc {suc q} i j eq with modq i
  modq-suc {suc q} i j () | just x
  modq-suc {suc q} i j () | nothing

  sucmod-inj : ∀ {q}{i j : Fin q} → sucmod i ≡ sucmod j → i ≡ j
  sucmod-inj {i = i} {j} eq with modq (suc i) | modq (suc j) | modq-inj (suc i) (suc j) | modq-suc i j | modq-suc j i
  sucmod-inj eq | just _  | just _  | p | _ | _ = suc-injective (p (cong just eq))
  sucmod-inj eq | nothing | nothing | p | _ | _ = suc-injective (p refl)
  sucmod-inj eq | just _  | nothing | _ | p | _ = ⊥-elim (p (cong Maybe.just eq))
  sucmod-inj eq | nothing | just _  | _ | _ | p = ⊥-elim (p (cong Maybe.just (sym eq)))

  modq-fromℕ : ∀ q → modq (fromℕ q) ≡ nothing
  modq-fromℕ zero = refl
  modq-fromℕ (suc q) rewrite modq-fromℕ q = refl

  modq-inject₁ : ∀ {q} (i : Fin q) → modq (inject₁ i) ≡ just i
  modq-inject₁ zero = refl
  modq-inject₁ (suc i) rewrite modq-inject₁ i = refl

  sucmod-fromℕ : ∀ q → sucmod (fromℕ q) ≡ zero
  sucmod-fromℕ q rewrite modq-fromℕ q = refl

  sucmod-inject₁ : ∀ {n} (i : Fin n) → sucmod (inject₁ i) ≡ suc i
  sucmod-inject₁ i rewrite modq-inject₁ i = refl

  lem-inject₁ : ∀ {n a} {A : Set a} (i : Fin n) (xs : Vec A n) x → lookup (inject₁ i) (xs ∷ʳ x) ≡ lookup i xs
  lem-inject₁ zero    (x₀ ∷ xs) x₁ = refl
  lem-inject₁ (suc i) (x₀ ∷ xs) x₁ = lem-inject₁ i xs x₁

  lem-fromℕ : ∀ {n a} {A : Set a} (xs : Vec A n) x → lookup (fromℕ n) (xs ∷ʳ x) ≡ x
  lem-fromℕ {zero}  []       x = refl
  lem-fromℕ {suc n} (_ ∷ xs) x = lem-fromℕ xs x

  lookup-sucmod : ∀ {n a} {A : Set a} (i : Fin (suc n)) (x : A) xs
                 → lookup i (xs ∷ʳ x) ≡ lookup (sucmod i) (x ∷ xs)
  lookup-sucmod i x xs with finView i
  lookup-sucmod {n} .(fromℕ n) x xs | `fromℕ rewrite sucmod-fromℕ n = lem-fromℕ xs x
  lookup-sucmod .(inject₁ x) x₁ xs | `inject₁ x rewrite sucmod-inject₁ x = lem-inject₁ x xs x₁

  lookup-map : ∀ {n a b} {A : Set a} {B : Set b} (f : A → B) i (xs : Vec A n)
               → lookup i (vmap f xs) ≡ f (lookup i xs)
  lookup-map f zero    (x ∷ xs) = refl
  lookup-map f (suc i) (x ∷ xs) = lookup-map f i xs

  vec≗⇒≡ : ∀ {n a} {A : Set a} (xs ys : Vec A n) → flip lookup xs ≗ flip lookup ys → xs ≡ ys
  vec≗⇒≡ []       []       _ = refl
  vec≗⇒≡ (x ∷ xs) (y ∷ ys) p rewrite vec≗⇒≡ xs ys (p ∘ suc) | p zero = refl

  -- most likely this is subsumed by the StableUnderInjection parts
  private
     module Unused where
        lookup-sucmod-rot₁ : ∀ {n a} {A : Set a} (i : Fin n) (xs : Vec A n)
                       → lookup i (rot₁ xs) ≡ lookup (sucmod i) xs
        lookup-sucmod-rot₁ {zero} () xs
        lookup-sucmod-rot₁ {suc n} i (x ∷ xs) = lookup-sucmod i x xs

        lookup-rot₁-allFin : ∀ {n} i → lookup i (rot₁ (allFin n)) ≡ lookup i (vmap sucmod (allFin n))
        lookup-rot₁-allFin {n} i rewrite lookup-sucmod-rot₁ i (allFin _)
                                       | Vec.lookup-allFin (sucmod i)
                                       | lookup-map sucmod i (allFin n)
                                       | Vec.lookup∘tabulate id i
                                       = refl

        rot₁-map-sucmod : ∀ n → rot₁ (allFin n) ≡ vmap sucmod (allFin n)
        rot₁-map-sucmod _ = vec≗⇒≡ _ _ lookup-rot₁-allFin

  {-

  -- -}
  -- -}
  -- -}
  -- -}
  -- -}
