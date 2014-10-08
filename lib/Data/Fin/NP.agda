-- NOTE with-K
module Data.Fin.NP where

open import Type hiding (★)
open import Function
open import Data.Zero
open import Data.One using (𝟙)
open import Data.Fin public renaming (toℕ to Fin▹ℕ)
open import Data.Nat.NP using (ℕ; zero; suc; _<=_; module ℕ°) renaming (_+_ to _+ℕ_)
open import Data.Two using (𝟚; 0₂; 1₂; [0:_1:_]; case_0:_1:_)
import Data.Vec.NP as Vec
open Vec using (Vec; []; _∷_; _∷ʳ_; allFin; lookup; rot₁; tabulate; foldr) renaming (map to vmap)
import Data.Vec.Properties as Vec
open import Data.Maybe.NP
open import Data.Sum as Sum
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as ≡

suc-injective : ∀ {m}{i j : Fin m} → Fin.suc i ≡ suc j → i ≡ j
suc-injective refl = refl

-- The isomorphisms about Fin, 𝟘, 𝟙, 𝟚 are in Function.Related.TypeIsomorphisms.NP

Fin▹𝟘 : Fin 0 → 𝟘
Fin▹𝟘 ()

𝟘▹Fin : 𝟘 → Fin 0
𝟘▹Fin ()

Fin▹𝟙 : Fin 1 → 𝟙
Fin▹𝟙 _ = _

𝟙▹Fin : 𝟙 → Fin 1
𝟙▹Fin _ = zero

Fin▹𝟚 : Fin 2 → 𝟚
Fin▹𝟚 zero    = 0₂
Fin▹𝟚 (suc _) = 1₂

𝟚▹Fin : 𝟚 → Fin 2
𝟚▹Fin = [0: # 0 1: # 1 ]

_+′_ : ∀ {m n} (x : Fin m) (y : Fin n) → Fin (m +ℕ n)
_+′_ {suc m} {n} zero y rewrite ℕ°.+-comm (suc m) n = inject+ _ y
suc x +′ y = suc (x +′ y)

_≟_ : ∀ {n} (i j : Fin n) → Dec (i ≡ j)
zero ≟ zero = yes refl
zero ≟ suc j = no (λ())
suc i ≟ zero = no (λ())
suc i ≟ suc j with i ≟ j
suc i ≟ suc j | yes p = yes (cong suc p)
suc i ≟ suc j | no ¬p = no (¬p ∘ suc-injective)

_==_ : ∀ {n} (x y : Fin n) → 𝟚
x == y = ⌊ x ≟ y ⌋
{-helper (compare x y) where
  helper : ∀ {n} {i j : Fin n} → Ordering i j → 𝟚
  helper (equal _) = 1₂
  helper _         = 0₂-}

swap : ∀ {i} (x y : Fin i) → Fin i → Fin i
swap x y z = case x == z 0: (case y == z 0: z 1: x) 1: y

module _ {a} {A : ★ a}
         (B : ℕ → ★₀)
         (_◅_ : ∀ {n} → A → B n → B (suc n))
         (ε : B zero) where
  iterate : ∀ {n} (f : Fin n → A) → B n
  iterate {zero}  f = ε
  iterate {suc n} f = f zero ◅ iterate (f ∘ suc)

  iterate-foldr∘tabulate :
    ∀ {n} (f : Fin n → A) → iterate f ≡ foldr B _◅_ ε (tabulate f)
  iterate-foldr∘tabulate {zero} f = refl
  iterate-foldr∘tabulate {suc n} f = cong (_◅_ (f zero)) (iterate-foldr∘tabulate (f ∘ suc))

module _ {a} {A : ★ a} (B : ★₀)
         (_◅_ : A → B → B)
         (ε : B) where
  iterate′ : ∀ {n} (f : Fin n → A) → B
  iterate′ f = iterate _ _◅_ ε f

data FinSum m n : Fin (m +ℕ n) → ★₀ where
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

{-
reverse-involutive : ∀ {n} (x : Fin n) → reverse (reverse x) ≡ x
reverse-involutive zero = reverse-fromℕ _
reverse-involutive (suc x) rewrite reverse-inject₁ (reverse x) | reverse-involutive x = refl
-}

reverse-lem : ∀ {n} (x : Fin n) → Fin▹ℕ (reverse x) ≡ n ∸ suc (Fin▹ℕ x)
reverse-lem zero = to-from _
reverse-lem (suc x) rewrite inject₁-lemma (reverse x) = reverse-lem x

Fin▹ℕ-ℕ-lem : ∀ {n} (x : Fin (suc n)) → Fin▹ℕ (n ℕ- x) ≡ n ∸ Fin▹ℕ x
Fin▹ℕ-ℕ-lem zero = to-from _
Fin▹ℕ-ℕ-lem {zero} (suc ())
Fin▹ℕ-ℕ-lem {suc n} (suc x) = Fin▹ℕ-ℕ-lem x

reverse-old-lem : ∀ {n} (x : Fin n) → Fin▹ℕ (reverse-old x) ≡ n ∸ suc (Fin▹ℕ x)
reverse-old-lem {zero} ()
reverse-old-lem {suc n} x rewrite inject≤-lemma (n ℕ- x) (n∸m≤n (Fin▹ℕ x) (suc n)) = Fin▹ℕ-ℕ-lem x

data FinView {n} : Fin (suc n) → ★₀ where
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
  sucmod-inj eq | just _  | nothing | _ | p | _ = 𝟘-elim (p (cong Maybe.just eq))
  sucmod-inj eq | nothing | just _  | _ | _ | p = 𝟘-elim (p (cong Maybe.just (sym eq)))

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

  lem-inject₁ : ∀ {n a} {A : ★ a} (i : Fin n) (xs : Vec A n) x → lookup (inject₁ i) (xs ∷ʳ x) ≡ lookup i xs
  lem-inject₁ zero    (x₀ ∷ xs) x₁ = refl
  lem-inject₁ (suc i) (x₀ ∷ xs) x₁ = lem-inject₁ i xs x₁

  lem-fromℕ : ∀ {n a} {A : ★ a} (xs : Vec A n) x → lookup (fromℕ n) (xs ∷ʳ x) ≡ x
  lem-fromℕ {zero}  []       x = refl
  lem-fromℕ {suc n} (_ ∷ xs) x = lem-fromℕ xs x

  lookup-sucmod : ∀ {n a} {A : ★ a} (i : Fin (suc n)) (x : A) xs
                 → lookup i (xs ∷ʳ x) ≡ lookup (sucmod i) (x ∷ xs)
  lookup-sucmod i x xs with finView i
  lookup-sucmod {n} .(fromℕ n) x xs | `fromℕ rewrite sucmod-fromℕ n = lem-fromℕ xs x
  lookup-sucmod .(inject₁ x) x₁ xs | `inject₁ x rewrite sucmod-inject₁ x = lem-inject₁ x xs x₁

  lookup-map : ∀ {n a b} {A : ★ a} {B : ★ b} (f : A → B) i (xs : Vec A n)
               → lookup i (vmap f xs) ≡ f (lookup i xs)
  lookup-map f zero    (x ∷ xs) = refl
  lookup-map f (suc i) (x ∷ xs) = lookup-map f i xs

  vec≗⇒≡ : ∀ {n a} {A : ★ a} (xs ys : Vec A n) → flip lookup xs ≗ flip lookup ys → xs ≡ ys
  vec≗⇒≡ []       []       _ = refl
  vec≗⇒≡ (x ∷ xs) (y ∷ ys) p rewrite vec≗⇒≡ xs ys (p ∘ suc) | p zero = refl

  -- most likely this is subsumed by the StableUnderInjection parts
  private
     module Unused where
        lookup-sucmod-rot₁ : ∀ {n a} {A : ★ a} (i : Fin n) (xs : Vec A n)
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
