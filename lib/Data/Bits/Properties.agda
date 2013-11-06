module Data.Bits.Properties where

open import Algebra.FunctionProperties.NP
open import Function
open import Type hiding (★)
open import Data.Zero using (𝟘; 𝟘-elim)
open import Data.Bit using (Bit)
open import Data.Two renaming (_==_ to _==ᵇ_)
import Data.Two.Equality as ==ᵇ
open import Data.Bits
open import Data.Nat.NP hiding (_==_) renaming (_<=_ to _ℕ<=_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Fin using (Fin; zero; suc)
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡
open import Data.Vec.NP

==-comm : ∀ {n} (xs ys : Bits n) → xs == ys ≡ ys == xs
==-comm [] [] = refl
==-comm (x ∷ xs) (y ∷ ys) rewrite ==ᵇ.comm x y | ==-comm xs ys = refl

==-refl : ∀ {n} (xs : Bits n) → (xs == xs) ≡ 1₂
==-refl [] = refl
==-refl (1₂ ∷ xs) = ==-refl xs
==-refl (0₂ ∷ xs) = ==-refl xs

vnot∘vnot≗id : ∀ {n} → vnot {n} ∘ vnot ≗ id
vnot∘vnot≗id [] = refl
vnot∘vnot≗id (x ∷ xs) rewrite not-involutive x | vnot∘vnot≗id xs = refl

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
        0ⁿ ⊕ 1ⁿ      ≡⟨ ⊕-left-identity 1ⁿ ⟩
        1ⁿ ∎ where open ≡-Reasoning

-- "Xor"ing the i-th bit with `b' is the same thing as "xor"ing with a vector of zeros
-- except at the i-th position.
-- Such a vector can be obtained by "xor"ing the i-th bit of a vector of zeros.
onᵢ-xor-⊕ : ∀ b {n} (i : Fin n) → onᵢ (_xor_ b) i ≗ _⊕_ (onᵢ (_xor_ b) i 0ⁿ)
onᵢ-xor-⊕ b zero    (x ∷ xs) rewrite proj₂ Xor°.+-identity b | ⊕-left-identity xs = refl
onᵢ-xor-⊕ b (suc i) (x ∷ xs) rewrite onᵢ-xor-⊕ b i xs = refl

∧°-comm : ∀ {n} (f g : Bits n → Bit) → f ∧° g ≗ g ∧° f
∧°-comm f g x with f x | g x
... | 0₂ | 0₂ = refl
... | 0₂ | 1₂ = refl
... | 1₂ | 0₂ = refl
... | 1₂ | 1₂ = refl

Bits▹ℕ-bound : ∀ {n} (xs : Bits n) → Bits▹ℕ xs < 2^ n 
Bits▹ℕ-bound         [] = s≤s z≤n
Bits▹ℕ-bound {suc n} (1₂ ∷ xs) rewrite +-assoc-comm 1 (2^ n) (Bits▹ℕ xs) = ℕ≤.refl {2^ n} +-mono Bits▹ℕ-bound xs
Bits▹ℕ-bound {suc n} (0₂ ∷ xs) = ≤-steps (2^ n) (Bits▹ℕ-bound xs)

Bits▹ℕ≤2ⁿ+ : ∀ {n} (x : Bits n) {y} → Bits▹ℕ {n} x ≤ 2^ n + y
Bits▹ℕ≤2ⁿ+ {n} x {y} = ℕ≤.trans (≤-steps y (≤-pred (≤-steps 1 (Bits▹ℕ-bound x))))
                             (ℕ≤.reflexive (ℕ°.+-comm y (2^ n)))

2ⁿ+≰Bits▹ℕ : ∀ {n x} (y : Bits n) → 2^ n + x ≰ Bits▹ℕ {n} y
2ⁿ+≰Bits▹ℕ {n} {x} y p = ¬n+≤y<n (2^ n) p (Bits▹ℕ-bound y)

Bits▹ℕ-inj : ∀ {n} (x y : Bits n) → Bits▹ℕ x ≡ Bits▹ℕ y → x ≡ y
Bits▹ℕ-inj         []        []        _ = refl
Bits▹ℕ-inj         (0₂ ∷ xs) (0₂ ∷ ys) p = cong 0∷_ (Bits▹ℕ-inj xs ys p)
Bits▹ℕ-inj {suc n} (1₂ ∷ xs) (1₂ ∷ ys) p = cong 1∷_ (Bits▹ℕ-inj xs ys (cancel-+-left (2^ n) p))
Bits▹ℕ-inj {suc n} (0₂ ∷ xs) (1₂ ∷ ys) p = 𝟘-elim (2ⁿ+≰Bits▹ℕ xs (ℕ≤.reflexive (≡.sym p)))
Bits▹ℕ-inj {suc n} (1₂ ∷ xs) (0₂ ∷ ys) p = 𝟘-elim (2ⁿ+≰Bits▹ℕ ys (ℕ≤.reflexive p))

data _≤ᴮ_ : ∀ {n} (p q : Bits n) → ★₀ where
  []    : [] ≤ᴮ []
  there : ∀ {n} {p q : Bits n} b → p ≤ᴮ q → (b ∷ p) ≤ᴮ (b ∷ q)
  0-1   : ∀ {n} (p q : Bits n) → 0∷ p ≤ᴮ 1∷ q

≤ᴮ→<= : ∀ {n} {p q : Bits n} → p ≤ᴮ q → ✓ (p <= q)
≤ᴮ→<= [] = _
≤ᴮ→<= (there 0₂ pf) = ≤ᴮ→<= pf
≤ᴮ→<= (there 1₂ pf) = ≤ᴮ→<= pf
≤ᴮ→<= (0-1 p q) = _

<=→≤ᴮ : ∀ {n} (p q : Bits n) → ✓ (p <= q) → p ≤ᴮ q
<=→≤ᴮ [] [] _ = []
<=→≤ᴮ (1₂ ∷ p) (0₂ ∷ q) ()
<=→≤ᴮ (0₂ ∷ p) (1₂ ∷ q) _  = 0-1 p q
<=→≤ᴮ (0₂ ∷ p) (0₂ ∷ q) pf = there 0₂ (<=→≤ᴮ p q pf)
<=→≤ᴮ (1₂ ∷ p) (1₂ ∷ q) pf = there 1₂ (<=→≤ᴮ p q pf)

Bits▹ℕ-≤-inj : ∀ {n} (x y : Bits n) → Bits▹ℕ x ≤ Bits▹ℕ y → x ≤ᴮ y
Bits▹ℕ-≤-inj     [] [] p = []
Bits▹ℕ-≤-inj         (0₂ ∷ xs) (0₂ ∷ ys) p = there 0₂ (Bits▹ℕ-≤-inj xs ys p)
Bits▹ℕ-≤-inj         (0₂ ∷ xs) (1₂ ∷ ys) p = 0-1 _ _
Bits▹ℕ-≤-inj {suc n} (1₂ ∷ xs) (0₂ ∷ ys) p = 𝟘-elim (2ⁿ+≰Bits▹ℕ ys p)
Bits▹ℕ-≤-inj {suc n} (1₂ ∷ xs) (1₂ ∷ ys) p = there 1₂ (Bits▹ℕ-≤-inj xs ys (+-≤-inj (2^ n) p))

funFromTbl∘tblFromFun : ∀ {n a} {A : ★ a} (fun : Bits n → A) → funFromTbl (tblFromFun fun) ≗ fun
funFromTbl∘tblFromFun {zero} f [] = refl
funFromTbl∘tblFromFun {suc n} f (0₂ ∷ xs)
  rewrite take-++ (2^ n) (tblFromFun {n} (f ∘ 0∷_)) (tblFromFun {n} (f ∘ 1∷_)) =
    funFromTbl∘tblFromFun {n} (f ∘ 0∷_) xs
funFromTbl∘tblFromFun {suc n} f (1₂ ∷ xs)
  rewrite drop-++ (2^ n) (tblFromFun {n} (f ∘ 0∷_)) (tblFromFun {n} (f ∘ 1∷_))
        | take-++ (2^ n) (tblFromFun {n} (f ∘ 1∷_)) [] =
    funFromTbl∘tblFromFun {n} (f ∘ 1∷_) xs

tblFromFun∘funFromTbl : ∀ {n a} {A : ★ a} (tbl : Vec A (2^ n)) → tblFromFun {n} (funFromTbl tbl) ≡ tbl
tblFromFun∘funFromTbl {zero} (x ∷ []) = refl
tblFromFun∘funFromTbl {suc n} tbl
  rewrite tblFromFun∘funFromTbl {n} (take _ tbl)
        | tblFromFun∘funFromTbl {n} (drop (2^ n) tbl)
        = take-drop-lem (2^ n) tbl

2ⁿ≰Bits▹ℕ : ∀ {n} (xs : Bits n) → 2^ n ≰ Bits▹ℕ xs
2ⁿ≰Bits▹ℕ xs p = ¬n≤x<n _ p (Bits▹ℕ-bound xs)

✓not2ⁿ<=Bits▹ℕ : ∀ {n} (xs : Bits n) → ✓ (not (2^ n ℕ<= (Bits▹ℕ xs)))
✓not2ⁿ<=Bits▹ℕ {n} xs with (2^ n) ℕ<= (Bits▹ℕ xs) | ≡.inspect (_ℕ<=_ (2^ n)) (Bits▹ℕ xs)
... | 1₂ | ≡.[ p ] = 2ⁿ≰Bits▹ℕ xs (<=.sound (2^ n) (Bits▹ℕ xs) (≡→✓ p))
... | 0₂ |     _   = _

ℕ▹Bits∘Bits▹ℕ : ∀ {n} (x : Bits n) → ℕ▹Bits (Bits▹ℕ x) ≡ x
ℕ▹Bits∘Bits▹ℕ [] = ≡.refl
ℕ▹Bits∘Bits▹ℕ {suc n} (1₂ ∷ xs)
  rewrite ✓→≡ (<=-steps′ {2^ n} (Bits▹ℕ xs))
        | ℕ°.+-comm (2^ n) (Bits▹ℕ xs)
        | m+n∸n≡m (Bits▹ℕ xs) (2^ n)
        | ℕ▹Bits∘Bits▹ℕ xs
        = ≡.refl
ℕ▹Bits∘Bits▹ℕ (0₂ ∷ xs)
  rewrite ✓not→≡ (✓not2ⁿ<=Bits▹ℕ xs)
        | ℕ▹Bits∘Bits▹ℕ xs
        = ≡.refl

Bits▹ℕ∘ℕ▹Bits : ∀ {n} x → x < 2^ n → Bits▹ℕ {n} (ℕ▹Bits x) ≡ x
Bits▹ℕ∘ℕ▹Bits {zero} .0 (s≤s z≤n) = ≡.refl
Bits▹ℕ∘ℕ▹Bits {suc n} x x<2ⁿ with 2^ n ℕ<= x | ≡.inspect (_ℕ<=_ (2^ n)) x
... | 1₂ | ≡.[ p ] rewrite Bits▹ℕ∘ℕ▹Bits {n} (x ∸ 2^ n) (x<2y→x∸y<y x (2^ n) x<2ⁿ) = m+n∸m≡n {2^ n} {x} (<=.sound (2^ n) x (≡→✓ p))
... | 0₂ | ≡.[ p ] = Bits▹ℕ∘ℕ▹Bits {n} x (<=.sound (suc x) (2^ n) (not<=→< (2^ n) x (≡→✓not p)))

ℕ▹Bits-inj : ∀ {n} {x y : ℕ} → x < 2^ n → y < 2^ n → ℕ▹Bits {n} x ≡ ℕ▹Bits y → x ≡ y
ℕ▹Bits-inj {n} {x} {y} x< y< fx≡fy
  = x
  ≡⟨ ≡.sym (Bits▹ℕ∘ℕ▹Bits {n} x x<) ⟩
    Bits▹ℕ (ℕ▹Bits {n} x)
  ≡⟨ ≡.cong Bits▹ℕ fx≡fy ⟩
    Bits▹ℕ (ℕ▹Bits {n} y)
  ≡⟨ Bits▹ℕ∘ℕ▹Bits {n} y y< ⟩
    y
  ∎ where open ≡-Reasoning
