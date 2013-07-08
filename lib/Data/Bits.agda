module Data.Bits where

open import Type hiding (★)
-- cleanup
import Level
open import Data.Nat.NP hiding (_==_) renaming (_<=_ to _ℕ<=_)
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Bit renaming (_==_ to _==ᵇ_; module == to ==ᵇ)
open import Data.Bool.Properties using (not-involutive)
import Data.Fin as Fin
open Fin using (Fin; zero; suc; #_; inject₁; inject+; raise) renaming (_+_ to _+ᶠ_)
import Data.Vec.NP as V
open V hiding (rewire; rewireTbl; sum) renaming (map to vmap; swap to vswap)
open import Data.Vec.N-ary.NP
open import Data.Zero using (𝟘; 𝟘-elim)
open import Data.Product using (_×_; _,_; uncurry; proj₁; proj₂)
open import Function.NP hiding (_→⟨_⟩_)
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡
open import Algebra.FunctionProperties.NP
import Data.List.NP as L

open import Data.Bool.NP public using (_xor_; not; true; false; if_then_else_)
open V public using ([]; _∷_; head; tail; replicate; RewireTbl)

Bits : ℕ → ★₀
Bits = Vec Bit

_→ᵇ_ : ℕ → ℕ → ★₀
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

_!_ : ∀ {a n} {A : ★ a} → Vec A n → Fin n → A
_!_ = flip lookup

_==_ : ∀ {n} (bs₀ bs₁ : Bits n) → Bit
[] == [] = true
(b₀ ∷ bs₀) == (b₁ ∷ bs₁) = (b₀ ==ᵇ b₁) ∧ bs₀ == bs₁

==-comm : ∀ {n} (xs ys : Bits n) → xs == ys ≡ ys == xs
==-comm [] [] = refl
==-comm (x ∷ xs) (y ∷ ys) rewrite ==ᵇ.comm x y | ==-comm xs ys = refl

==-refl : ∀ {n} (xs : Bits n) → (xs == xs) ≡ 1b
==-refl [] = refl
==-refl (true ∷ xs) = ==-refl xs
==-refl (false ∷ xs) = ==-refl xs

_<=_ : ∀ {n} (xs ys : Bits n) → Bit
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
        0ⁿ ⊕ 1ⁿ      ≡⟨ ⊕-left-identity 1ⁿ ⟩
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
 -- ⊛-dist-∙ : ∀ {n a} {A : ★ a} (fs : Vec (A → A) n) π xs → π ∙ fs ⊛ π ∙ xs ≡ π ∙ (fs ⊛ xs)
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

view∷ : ∀ {n a b} {A : ★ a} {B : ★ b} → (A → Vec A n → B) → Vec A (suc n) → B
view∷ f (x ∷ xs) = f x xs

sucBCarry : ∀ {n} → Bits n → Bits (1 + n)
sucBCarry []        = 0b ∷ []
sucBCarry (0b ∷ xs) = 0b ∷ sucBCarry xs
sucBCarry (1b ∷ xs) = view∷ (λ x xs → x ∷ not x ∷ xs) (sucBCarry xs)

sucB : ∀ {n} → Bits n → Bits n
sucB = tail ∘ sucBCarry

--_[mod_] : ℕ → ℕ → ★₀
--a [mod b ] = DivMod' a b

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
toℕ-inj {suc n} (0b ∷ xs) (1b ∷ ys) p = 𝟘-elim (2ⁿ+≰toℕ xs (ℕ≤.reflexive (≡.sym p)))
toℕ-inj {suc n} (1b ∷ xs) (0b ∷ ys) p = 𝟘-elim (2ⁿ+≰toℕ ys (ℕ≤.reflexive p))

data _≤ᴮ_ : ∀ {n} (p q : Bits n) → ★₀ where
  []    : [] ≤ᴮ []
  there : ∀ {n} {p q : Bits n} b → p ≤ᴮ q → (b ∷ p) ≤ᴮ (b ∷ q)
  0-1   : ∀ {n} (p q : Bits n) → 0∷ p ≤ᴮ 1∷ q

≤ᴮ→<= : ∀ {n} {p q : Bits n} → p ≤ᴮ q → ✓ (p <= q)
≤ᴮ→<= [] = _
≤ᴮ→<= (there 0b pf) = ≤ᴮ→<= pf
≤ᴮ→<= (there 1b pf) = ≤ᴮ→<= pf
≤ᴮ→<= (0-1 p q) = _

<=→≤ᴮ : ∀ {n} (p q : Bits n) → ✓ (p <= q) → p ≤ᴮ q
<=→≤ᴮ [] [] _ = []
<=→≤ᴮ (1b ∷ p) (0b ∷ q) ()
<=→≤ᴮ (0b ∷ p) (1b ∷ q) _  = 0-1 p q
<=→≤ᴮ (0b ∷ p) (0b ∷ q) pf = there 0b (<=→≤ᴮ p q pf)
<=→≤ᴮ (1b ∷ p) (1b ∷ q) pf = there 1b (<=→≤ᴮ p q pf)

toℕ-≤-inj : ∀ {n} (x y : Bits n) → toℕ x ≤ toℕ y → x ≤ᴮ y
toℕ-≤-inj     [] [] p = []
toℕ-≤-inj         (0b ∷ xs) (0b ∷ ys) p = there 0b (toℕ-≤-inj xs ys p)
toℕ-≤-inj         (0b ∷ xs) (1b ∷ ys) p = 0-1 _ _
toℕ-≤-inj {suc n} (1b ∷ xs) (0b ∷ ys) p = 𝟘-elim (2ⁿ+≰toℕ ys p)
toℕ-≤-inj {suc n} (1b ∷ xs) (1b ∷ ys) p = there 1b (toℕ-≤-inj xs ys (+-≤-inj (2^ n) p))

fromℕ : ∀ {n} → ℕ → Bits n
fromℕ {zero}  _ = []
fromℕ {suc n} x = if 2^ n ℕ<= x then 1∷ fromℕ (x ∸ 2^ n) else 0∷ fromℕ x

fromℕ′ : ∀ {n} → ℕ → Bits n
fromℕ′ = fold 0ⁿ sucB

fromFin : ∀ {n} → Fin (2^ n) → Bits n
fromFin = fromℕ ∘ Fin.toℕ

lookupTbl : ∀ {n a} {A : ★ a} → Bits n → Vec A (2^ n) → A
lookupTbl         []         (x ∷ []) = x
lookupTbl         (0b ∷ key) tbl      = lookupTbl key (take _ tbl)
lookupTbl {suc n} (1b ∷ key) tbl      = lookupTbl key (drop (2^ n) tbl)

funFromTbl : ∀ {n a} {A : ★ a} → Vec A (2^ n) → (Bits n → A)
funFromTbl = flip lookupTbl

tblFromFun : ∀ {n a} {A : ★ a} → (Bits n → A) → Vec A (2^ n)
-- tblFromFun f = tabulate (f ∘ fromFin)
tblFromFun {zero} f = f [] ∷ []
tblFromFun {suc n} f = tblFromFun {n} (f ∘ 0∷_) ++ tblFromFun {n} (f ∘ 1∷_)

funFromTbl∘tblFromFun : ∀ {n a} {A : ★ a} (fun : Bits n → A) → funFromTbl (tblFromFun fun) ≗ fun
funFromTbl∘tblFromFun {zero} f [] = refl
funFromTbl∘tblFromFun {suc n} f (0b ∷ xs)
  rewrite take-++ (2^ n) (tblFromFun {n} (f ∘ 0∷_)) (tblFromFun {n} (f ∘ 1∷_)) =
    funFromTbl∘tblFromFun {n} (f ∘ 0∷_) xs
funFromTbl∘tblFromFun {suc n} f (1b ∷ xs)
  rewrite drop-++ (2^ n) (tblFromFun {n} (f ∘ 0∷_)) (tblFromFun {n} (f ∘ 1∷_))
        | take-++ (2^ n) (tblFromFun {n} (f ∘ 1∷_)) [] =
    funFromTbl∘tblFromFun {n} (f ∘ 1∷_) xs

tblFromFun∘funFromTbl : ∀ {n a} {A : ★ a} (tbl : Vec A (2^ n)) → tblFromFun {n} (funFromTbl tbl) ≡ tbl
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

✓not2ⁿ<=toℕ : ∀ {n} (xs : Bits n) → ✓ (not (2^ n ℕ<= (toℕ xs)))
✓not2ⁿ<=toℕ {n} xs with (2^ n) ℕ<= (toℕ xs) | ≡.inspect (_ℕ<=_ (2^ n)) (toℕ xs)
... | true  | ≡.[ p ] = 2ⁿ≰toℕ xs (<=.sound (2^ n) (toℕ xs) (≡→✓ p))
... | false |     _   = _

fromℕ∘toℕ : ∀ {n} (x : Bits n) → fromℕ (toℕ x) ≡ x
fromℕ∘toℕ [] = ≡.refl
fromℕ∘toℕ {suc n} (true ∷ xs)
  rewrite ✓→≡ (<=-steps′ {2^ n} (toℕ xs))
        | ℕ°.+-comm (2^ n) (toℕ xs)
        | m+n∸n≡m (toℕ xs) (2^ n)
        | fromℕ∘toℕ xs
        = ≡.refl
fromℕ∘toℕ (false ∷ xs)
  rewrite ✓not→≡ (✓not2ⁿ<=toℕ xs)
        | fromℕ∘toℕ xs
        = ≡.refl

toℕ∘fromℕ : ∀ {n} x → x < 2^ n → toℕ {n} (fromℕ x) ≡ x
toℕ∘fromℕ {zero} .0 (s≤s z≤n) = ≡.refl
toℕ∘fromℕ {suc n} x x<2ⁿ with 2^ n ℕ<= x | ≡.inspect (_ℕ<=_ (2^ n)) x
... | true  | ≡.[ p ] rewrite toℕ∘fromℕ {n} (x ∸ 2^ n) (x<2y→x∸y<y x (2^ n) x<2ⁿ) = m+n∸m≡n {2^ n} {x} (<=.sound (2^ n) x (≡→✓ p))
... | false | ≡.[ p ] = toℕ∘fromℕ {n} x (<=.sound (suc x) (2^ n) (not<=→< (2^ n) x (≡→✓not p)))

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
