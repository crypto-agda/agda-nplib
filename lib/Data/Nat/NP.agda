{-# OPTIONS --universe-polymorphism #-}
module Data.Nat.NP where

import Algebra
open import Data.Nat public hiding (module GeneralisedArithmetic; module ≤-Reasoning; fold)
open import Data.Nat.Properties as Props
open import Data.Nat.Logical
open import Data.Bool
open import Data.Product using (proj₁; proj₂; ∃; _,_)
open import Data.Empty using (⊥-elim)
open import Function.NP
open import Relation.Nullary
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_; module ≡-Reasoning)

module ℕ°   = Algebra.CommutativeSemiring Props.commutativeSemiring
module ℕcmp = StrictTotalOrder Props.strictTotalOrder
module ℕ≤   = DecTotalOrder    decTotalOrder
module ⊔°   = Algebra.CommutativeSemiringWithoutOne ⊔-⊓-0-commutativeSemiringWithoutOne

module ≤-Reasoning where
  open Preorder-Reasoning ℕ≤.preorder public renaming (_∼⟨_⟩_ to _≤⟨_⟩_)
  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ x {y z : ℕ} → x ≡ y → y ≤ z → x ≤ z
  _ ≡⟨ ≡.refl ⟩ p = p
  infixr 2 _<⟨_⟩_
  _<⟨_⟩_ : ∀ x {y z : ℕ} → x < y → y ≤ z → x < z
  x <⟨ p ⟩ q = suc x ≤⟨ p ⟩ q

suc-injective : ∀ {n m : ℕ} → (suc n ∶ ℕ) ≡ suc m → n ≡ m
suc-injective = ≡.cong pred

fold : ∀ {a} {A : Set a} → A → Endo A → ℕ → A
fold x f n = nest n f x

2*_ : ℕ → ℕ
2* x = x + x

2*-spec : ∀ n → 2* n ≡ 2 * n
2*-spec n rewrite ℕ°.+-comm n 0 = ≡.refl

_==_ : (x y : ℕ) → Bool
zero   == zero   = true
zero   == suc _  = false
suc _  == zero   = false
suc m  == suc n  = m == n

assoc-comm : ∀ x y z → x + (y + z) ≡ y + (x + z)
assoc-comm x y z rewrite ≡.sym (ℕ°.+-assoc x y z)
                       | ℕ°.+-comm x y
                       | ℕ°.+-assoc y x z = ≡.refl

2*′_ : ℕ → ℕ
2*′_ = fold 0 (suc ∘′ suc)

2*′-spec : ∀ n → 2*′ n ≡ 2* n
2*′-spec zero = ≡.refl
2*′-spec (suc n) rewrite 2*′-spec n | assoc-comm 1 n n = ≡.refl

dist : ℕ → ℕ → ℕ
dist zero    y       = y
dist x       zero    = x
dist (suc x) (suc y) = dist x y

dist-refl : ∀ x → dist x x ≡ 0
dist-refl zero = ≡.refl
dist-refl (suc x) rewrite dist-refl x = ≡.refl

dist-0≡id : ∀ x → dist 0 x ≡ x
dist-0≡id _ = ≡.refl

dist-x-x+y≡y : ∀ x y → dist x (x + y) ≡ y
dist-x-x+y≡y zero    y = ≡.refl
dist-x-x+y≡y (suc x) y = dist-x-x+y≡y x y

dist-sym : ∀ x y → dist x y ≡ dist y x
dist-sym zero zero = ≡.refl
dist-sym zero (suc y) = ≡.refl
dist-sym (suc x) zero = ≡.refl
dist-sym (suc x) (suc y) = dist-sym x y

dist-x+ : ∀ x y z → dist (x + y) (x + z) ≡ dist y z
dist-x+ zero    y z = ≡.refl
dist-x+ (suc x) y z = dist-x+ x y z

dist-2* : ∀ x y → dist (2* x) (2* y) ≡ 2* dist x y
dist-2* zero y = ≡.refl
dist-2* (suc x) zero = ≡.refl
dist-2* (suc x) (suc y) rewrite assoc-comm x 1 x
                              | assoc-comm y 1 y = dist-2* x y

dist-asym-def : ∀ {x y} → x ≤ y → x + dist x y ≡ y
dist-asym-def z≤n = ≡.refl
dist-asym-def (s≤s pf) = ≡.cong suc (dist-asym-def pf)

dist-sym-wlog : ∀ (f : ℕ → ℕ) → (∀ x k → dist (f x) (f (x + k)) ≡ f k) → ∀ x y → dist (f x) (f y) ≡ f (dist x y)
dist-sym-wlog f pf x y with compare x y
dist-sym-wlog f pf x .(suc (x + k)) | less .x k with pf x (suc k)
... | q rewrite assoc-comm x 1 k | q | ≡.sym (assoc-comm x 1 k) | dist-x-x+y≡y x (suc k) = ≡.refl
dist-sym-wlog f pf .y y | equal .y with pf y 0
... | q rewrite ℕ°.+-comm y 0 | dist-refl y = q
dist-sym-wlog f pf .(suc (y + k)) y | greater .y k with pf y (suc k)
... | q rewrite assoc-comm 1 y k | dist-sym (y + suc k) y | dist-x-x+y≡y y (suc k) | dist-sym (f (y + suc k)) (f y) = q

dist-x* : ∀ x y z → dist (x * y) (x * z) ≡ x * dist y z
dist-x* x = dist-sym-wlog (_*_ x) pf
  where pf : ∀ a k → dist (x * a) (x * (a + k)) ≡ x * k
        pf a k rewrite proj₁ ℕ°.distrib x a k = dist-x-x+y≡y (x * a) _

2^⟨_⟩* : ℕ → ℕ → ℕ
2^⟨ n ⟩* x = fold x 2*_ n

⟨2^_*_⟩ : ℕ → ℕ → ℕ
⟨2^ n * x ⟩ = 2^⟨ n ⟩* x

2*-distrib : ∀ x y → 2* x + 2* y ≡ 2* (x + y) 
2*-distrib = solve 2 (λ x y → 2:* x :+ 2:* y := 2:* (x :+ y)) ≡.refl
      where open SemiringSolver
            2:* : ∀ {n} → Polynomial n → Polynomial n
            2:* x = x :+ x

2^*-distrib : ∀ k x y → ⟨2^ k * (x + y)⟩ ≡ ⟨2^ k * x ⟩ + ⟨2^ k * y ⟩
2^*-distrib zero x y = ≡.refl
2^*-distrib (suc k) x y rewrite 2^*-distrib k x y = ≡.sym (2*-distrib ⟨2^ k * x ⟩ ⟨2^ k * y ⟩)

2^*-2*-comm : ∀ k x → ⟨2^ k * 2* x ⟩ ≡ 2* ⟨2^ k * x ⟩
2^*-2*-comm k x = 2^*-distrib k x x

dist-2^* : ∀ x y z → dist ⟨2^ x * y ⟩ ⟨2^ x * z ⟩ ≡ ⟨2^ x * dist y z ⟩
dist-2^* x = dist-sym-wlog (2^⟨ x ⟩*) pf
  where pf : ∀ a k → dist ⟨2^ x * a ⟩ ⟨2^ x * (a + k) ⟩ ≡ ⟨2^ x * k ⟩
        pf a k rewrite 2^*-distrib x a k = dist-x-x+y≡y ⟨2^ x * a ⟩ ⟨2^ x * k ⟩

2*-mono : ∀ {a b} → a ≤ b → 2* a ≤ 2* b
2*-mono pf = pf +-mono pf

2^*-mono : ∀ k {a b} → a ≤ b → ⟨2^ k * a ⟩ ≤ ⟨2^ k * b ⟩
2^*-mono zero    pf = pf
2^*-mono (suc k) pf = 2*-mono (2^*-mono k pf)

2*-mono′ : ∀ {a b} → 2* a ≤ 2* b → a ≤ b
2*-mono′ {zero} pf = z≤n
2*-mono′ {suc a} {zero} ()
2*-mono′ {suc a} {suc b} pf rewrite assoc-comm a 1 a
                                  | assoc-comm b 1 b = s≤s (2*-mono′ (≤-pred (≤-pred pf)))

2^*-mono′ : ∀ k {a b} → ⟨2^ k * a ⟩ ≤ ⟨2^ k * b ⟩ → a ≤ b
2^*-mono′ zero    = id
2^*-mono′ (suc k) = 2^*-mono′ k ∘ 2*-mono′

2^-comm : ∀ x y z → ⟨2^ x * ⟨2^ y * z ⟩ ⟩ ≡ ⟨2^ y * ⟨2^ x * z ⟩ ⟩
2^-comm zero y z = ≡.refl
2^-comm (suc x) y z rewrite 2^-comm x y z = ≡.sym (2^*-2*-comm y ⟨2^ x * z ⟩)

2^-+ : ∀ x y z → ⟨2^ x * ⟨2^ y * z ⟩ ⟩ ≡ ⟨2^ (x + y) * z ⟩
2^-+ zero    y z = ≡.refl
2^-+ (suc x) y z = ≡.cong 2*_ (2^-+ x y z)

2*′-inj : ∀ {m n} → ⟦ℕ⟧ (2*′ m) (2*′ n) → ⟦ℕ⟧ m n
2*′-inj {zero}  {zero}  _ = zero
2*′-inj {zero}  {suc _} ()
2*′-inj {suc _} {zero}  ()
2*′-inj {suc m} {suc n} (suc (suc p)) = suc (2*′-inj p)

2*-inj : ∀ {m n} → 2* m ≡ 2* n → m ≡ n
2*-inj {m} {n} p rewrite ≡.sym (2*′-spec m)
                       | ≡.sym (2*′-spec n)
                       = ⟦ℕ⟧⇒≡ (2*′-inj (⟦ℕ⟧ˢ.reflexive p))

2^-inj : ∀ k {m n} → ⟨2^ k * m ⟩ ≡ ⟨2^ k * n ⟩ → m ≡ n
2^-inj zero    = id
2^-inj (suc k) = 2^-inj k ∘ 2*-inj

2ⁿ*0≡0 : ∀ n → ⟨2^ n * 0 ⟩ ≡ 0
2ⁿ*0≡0 zero    = ≡.refl
2ⁿ*0≡0 (suc n) = ≡.cong₂ _+_ (2ⁿ*0≡0 n) (2ⁿ*0≡0 n)

0∸_≡0 : ∀ x → 0 ∸ x ≡ 0
0∸ zero  ≡0 = ≡.refl
0∸ suc x ≡0 = ≡.refl

2*-∸ : ∀ x y → 2* x ∸ 2* y ≡ 2* (x ∸ y)
2*-∸ _       zero    = ≡.refl
2*-∸ zero    (suc _) = ≡.refl
2*-∸ (suc x) (suc y) rewrite ≡.sym (2*-∸ x y) | ℕ°.+-comm x (1 + x) | ℕ°.+-comm y (1 + y) = ≡.refl

n+k∸m : ∀ {m n} k → m ≤ n → n + k ∸ m ≡ (n ∸ m) + k
n+k∸m k z≤n = ≡.refl
n+k∸m k (s≤s m≤n) = n+k∸m k m≤n

factor-+-∸ : ∀ {b x y} → x ≤ b → y ≤ b → (b ∸ x) + (b ∸ y) ≡ 2* b ∸ (x + y)
factor-+-∸ {b} {zero} {y} z≤n y≤b rewrite ℕ°.+-comm b (b ∸ y) = ≡.sym (n+k∸m b y≤b)
factor-+-∸ (s≤s {x} {b} x≤b) z≤n             rewrite ℕ°.+-comm x 0 = ≡.sym (n+k∸m (suc b) x≤b)
factor-+-∸ (s≤s {x} {b} x≤b) (s≤s {y} y≤b)   rewrite factor-+-∸ x≤b y≤b
                                              | ℕ°.+-comm b (suc b)
                                              | ℕ°.+-comm x (suc y)
                                              | n+k∸m (suc y) x≤b
                                              | ℕ°.+-comm x y = ≡.refl

{-
post--ulate
  dist-sum   : ∀ x y z → dist x y + dist y z ≤ dist x z
  dist-≤     : ∀ x y → dist x y ≤ x
  dist-mono₁ : ∀ x y z t → x ≤ y → dist z t ≤ dist (x + z) (y + t)
-}

-- Haskell
-- let dist x y = abs (x - y)
-- quickCheck (forAll (replicateM 3 (choose (0,100))) (\ [x,y,z] -> dist (x * y) (x * z) == x * dist y z))

infix 8 _^_
_^_ : ℕ → ℕ → ℕ
b ^ zero  = 1
b ^ suc n = b * b ^ n

2^_ : ℕ → ℕ
2^ n = ⟨2^ n * 1 ⟩

2^-spec : ∀ n → 2^ n ≡ 2 ^ n
2^-spec zero = ≡.refl
2^-spec (suc n) rewrite 2^-spec n | 2*-spec (2 ^ n) = ≡.refl

-- https://en.wikipedia.org/wiki/Hyper_operator
_↑⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
a ↑⟨ suc n             ⟩ (suc b) = a ↑⟨ n ⟩ (a ↑⟨ suc n ⟩ b)
a ↑⟨ 0                 ⟩ b       = suc b
a ↑⟨ 1                 ⟩ 0       = a
a ↑⟨ 2                 ⟩ 0       = 0
a ↑⟨ suc (suc (suc n)) ⟩ 0       = 1

module ↑-Props where
  ↑-fold : ∀ a n b → a ↑⟨ suc n ⟩ b ≡ fold (a ↑⟨ suc n ⟩ 0) (_↑⟨_⟩_ a n) b
  ↑-fold a n zero = ≡.refl
  ↑-fold a n (suc b) = ≡.cong (_↑⟨_⟩_ a n) (↑-fold a n b)

  ↑₀-+ : ∀ a b → a ↑⟨ 0 ⟩ b ≡ 1 + b
  ↑₀-+ a b = ≡.refl

  ↑₁-+ : ∀ a b → a ↑⟨ 1 ⟩ b ≡ b + a
  ↑₁-+ a zero    = ≡.refl
  ↑₁-+ a (suc b) = ≡.cong suc (↑₁-+ a b)

  ↑₂-* : ∀ a b → a ↑⟨ 2 ⟩ b ≡ b * a
  ↑₂-* a zero    = ≡.refl
  ↑₂-* a (suc b) rewrite ↑₂-* a b
                       | ↑₁-+ a (b * a)
                       | ℕ°.+-comm (b * a) a
                       = ≡.refl

  -- fold 1 (_*_ a) b ≡ a ^ b
  ↑₃-^ : ∀ a b → a ↑⟨ 3 ⟩ b ≡ a ^ b
  ↑₃-^ a zero = ≡.refl
  ↑₃-^ a (suc b) rewrite ↑₃-^ a b
                       | ↑₂-* a (a ^ b)
                       | ℕ°.*-comm (a ^ b) a
                       = ≡.refl

  _↑⟨_⟩0 : ℕ → ℕ → ℕ
  a ↑⟨ 0                 ⟩0 = 1
  a ↑⟨ 1                 ⟩0 = a
  a ↑⟨ 2                 ⟩0 = 0
  a ↑⟨ suc (suc (suc n)) ⟩0 = 1

  _`↑⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
  _`↑⟨_⟩_ a 0       = suc
  _`↑⟨_⟩_ a (suc n) = fold (a ↑⟨ suc n ⟩0) (_`↑⟨_⟩_ a n)

  ↑-ind-rule : ∀ a n b → a ↑⟨ suc n ⟩ (suc b) ≡ a ↑⟨ n ⟩ (a ↑⟨ suc n ⟩ b)
  ↑-ind-rule a n b = ≡.refl

  _↑′⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
  a ↑′⟨ 0 ⟩ b = suc b
  a ↑′⟨ 1 ⟩ b = a + b
  a ↑′⟨ 2 ⟩ b = a * b
  a ↑′⟨ 3 ⟩ b = a ^ b
  a ↑′⟨ suc (suc (suc (suc n))) ⟩ b = a ↑⟨ 4 + n ⟩ b

  ↑-↑′ : ∀ a n b → a ↑⟨ n ⟩ b ≡ a ↑′⟨ n ⟩ b
  ↑-↑′ a 0 b = ≡.refl
  ↑-↑′ a 1 b = ≡.trans (↑₁-+ a b) (ℕ°.+-comm b a)
  ↑-↑′ a 2 b = ≡.trans (↑₂-* a b) (ℕ°.*-comm b a)
  ↑-↑′ a 3 b = ↑₃-^ a b
  ↑-↑′ a (suc (suc (suc (suc _)))) b = ≡.refl

  _↑2+⟨_⟩_ : ℕ → ℕ → ℕ → ℕ
  _↑2+⟨_⟩_ a = fold (_*_ a) (fold 1)

module InflModule where
  -- Inflationary functions
  Infl< : (f : ℕ → ℕ) → Set
  Infl< f = ∀ {x} → x < f x

  Infl : (f : ℕ → ℕ) → Set
  Infl f = Infl< (suc ∘ f)

  InflT< : (f : Endo (Endo ℕ)) → Set
  InflT< f = ∀ {g} → Infl< g → Infl< (f g)

{-
∀ {x} → x ≤ f x


  1 + x ≤ 1 + f x
  x < 1 + f x
  x < (suc ∘ f) x
  Infl< (suc ∘ f)

  Infl< f = ∀ {x} → 1 + x ≤ f x
  Infl< f = ∀ {x} → 1 + x ≤ f x

Infl< f → Infl f
Infl< f → Infl< (suc ∘ f)
-}

  id-infl : Infl id
  id-infl = ℕ≤.refl

  ∘-infl< : ∀ {f g} → Infl< f → Infl< g → Infl< (f ∘ g)
  ∘-infl< inflf< inflg< = <-trans inflg< inflf<

  suc-infl< : Infl< suc
  suc-infl< = ℕ≤.refl

  suc-infl : Infl suc
  suc-infl = s≤s (≤-step ℕ≤.refl)

  nest-infl : ∀ f (finfl : Infl f) n → Infl (nest n f)
  nest-infl f _ zero = ℕ≤.refl
  nest-infl f finfl (suc n) = ℕ≤.trans (nest-infl f finfl n) finfl

  nest-infl< : ∀ f (finfl< : Infl< f) n → Infl< (nest (suc n) f)
  nest-infl< f finfl< zero = finfl<
  nest-infl< f finfl< (suc n) = <-trans (nest-infl< f finfl< n) finfl< 

-- See Function.NP.nest-Properties for more properties
module fold-Props where

  fold-suc : ∀ m n → fold m suc n ≡ n + m
  fold-suc m zero = ≡.refl
  fold-suc m (suc n) rewrite fold-suc m n = ≡.refl

  fold-+ : ∀ m n → fold 0 (_+_ m) n ≡ n * m
  fold-+ m zero = ≡.refl
  fold-+ m (suc n) rewrite fold-+ m n = ≡.refl

  fold-* : ∀ m n → fold 1 (_*_ m) n ≡ m ^ n
  fold-* m zero = ≡.refl
  fold-* m (suc n) rewrite fold-* m n = ≡.refl

{- TODO
  fold-^ : ∀ m n → fold 1 (flip _^_ m) n ≡ m ↑⟨ 4 ⟩ n
  fold-^ m zero = ≡.refl
  fold-^ m (suc n) rewrite fold-^ m n = ?
-}

  cong-fold : ∀ {A : Set} {f g : Endo A} (f≗g : f ≗ g) {z} → fold z f ≗ fold z g
  cong-fold eq zero = ≡.refl
  cong-fold eq {z} (suc x) rewrite cong-fold eq {z} x = eq _

  private
   open ↑-Props
   module Alt↑2 where
    alt : ℕ → ℕ → ℕ → ℕ
    alt a 0       = λ b → a ↑⟨ 2 ⟩ b
    alt a (suc n) = fold 1 (alt a n)

    alt-ok : ∀ a n → _↑2+⟨_⟩_ a n ≗ alt a n
    alt-ok a zero = ≡.sym ∘ ↑-↑′ a 2
    alt-ok a (suc n) = cong-fold (alt-ok a n)

{- TODO
    alt' : ∀ a n → _↑2+⟨_⟩_ a n ≗ _↑⟨_⟩_ a (2 + n)
    alt' a zero  b = ≡.sym (↑-↑′ a 2 _)
    alt' a (suc n) zero = ≡.refl
    alt' a (suc n) (suc x) rewrite alt' a n (_↑2+⟨_⟩_ a (suc n) x)
       = ≡.cong (_↑⟨_⟩_ a (2 + n)) { fold 1 (fold (_*_ a) (fold 1) n) x} {a ↑⟨ suc (suc (suc n)) ⟩ x} (alt' a (suc n) x)
-}

  open InflModule
{-
  fold1-infl : ∀ f → Infl f → Infl (fold 1 f)
  fold1-infl f finfl {zero} = {!z≤n!}
  fold1-infl f finfl {suc x} =
     x          <⟨ {!s≤s (fold1-infl f finfl {x})!} ⟩
     fold 1 f x <⟨ {!!} ⟩
     {- f (fold 1 f x) ≤⟨ finfl ⟩
     f (fold 1 f x) ≡⟨ ≡.refl ⟩ -}
     fold 1 f (1 + x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}

{-
  fold1+1-infl< : ∀ (f : ℕ → ℕ) → Infl< (f ∘ suc) → Infl< (fold 1 f ∘ suc)
  fold1+1-infl< f finfl< {zero} = finfl<
  fold1+1-infl< f finfl< {suc x} =
     2 + x ≤⟨ s≤s (fold1+1-infl< f finfl< {x}) ⟩
     1 + f (fold 1 f x) ≤⟨ finfl< {f (fold 1 f x)} ⟩
     f (suc (f (fold 1 f x))) ≤⟨ {!!} ⟩
     fold 1 f (2 + x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
{-
  fold1+1-infl< : ∀ (f : ℕ → ℕ) → Infl< (f ∘ suc) → Infl< (fold 1 (f ∘ suc))
  fold1+1-infl< f finfl< {zero} = s≤s z≤n
  fold1+1-infl< f finfl< {suc x} =
     2 + x ≤⟨ s≤s (fold1+1-infl< f finfl< {x}) ⟩
     1 + fold 1 (f ∘ suc) x ≤⟨ finfl< ⟩
     fold 1 (f ∘ suc) (suc x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
{-
  fold1+-infl< : ∀ k f → Infl< (f ∘′ _+_ k) → Infl< (fold 1 (f ∘′ _+_ k))
  fold1+-infl< k f finfl< {zero} = s≤s z≤n
  fold1+-infl< k f finfl< {suc x} =
     2 + x ≤⟨ s≤s (fold1+-infl< k f finfl< {x}) ⟩
     1 + fold 1 (f ∘ _+_ k) x ≤⟨ finfl< ⟩
     fold 1 (f ∘ _+_ k) (suc x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
  
{-
  fold1+-infl< : ∀ f → Infl+2< f → Infl+2< (fold 1 f)
  fold1+-infl< f finfl< {zero} _ = ℕ≤.refl
  fold1+-infl< f finfl< {suc zero} _ = {!!}
  fold1+-infl< f finfl< {suc (suc zero)} _ = {!!}
  fold1+-infl< f finfl< {suc (suc (suc x))} x>1 =
     4 + x ≤⟨ s≤s (fold1+-infl< f finfl< {suc (suc x)} (m≤m+n 2 x)) ⟩
     1 + fold 1 f (2 + x) ≤⟨ finfl< {!!} ⟩
     fold 1 f (3 + x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
{-
  fold1-infl< f finfl< {zero} = s≤s z≤n
  fold1-infl< f finfl< {suc x} =
     2 + x ≤⟨ s≤s (fold1-infl< f finfl< {x}) ⟩
     1 + fold 1 f x ≤⟨ finfl< ⟩
     fold 1 f (suc x)
   ∎
     where
       open Props
       open ≤-Reasoning
-}
module ^-Props where
  open ≡-Reasoning

  ^1 : ∀ n → n ^ 1 ≡ n
  ^1 zero = ≡.refl
  ^1 (suc n) = ≡.cong suc (proj₂ ℕ°.*-identity n)

  ^-+ : ∀ b m n → b ^ (m + n) ≡ b ^ m * b ^ n
  ^-+ b zero n = ≡.sym (proj₂ ℕ°.+-identity (b ^ n))
  ^-+ b (suc m) n rewrite ^-+ b m n = ≡.sym (ℕ°.*-assoc b (b ^ m) (b ^ n))

  ^-* : ∀ b m n → b ^ (m * n) ≡ (b ^ n) ^ m
  ^-* b zero    n = ≡.refl
  ^-* b (suc m) n = b ^ (n + m * n)
                  ≡⟨ ^-+ b n (m * n) ⟩
                    b ^ n * b ^ (m * n)
                  ≡⟨ ≡.cong (_*_ (b ^ n)) (^-* b m n) ⟩
                    b ^ n * (b ^ n) ^ m ∎

ack : ℕ → ℕ → ℕ
ack zero n          = suc n
ack (suc m) zero    = ack m (suc zero)
ack (suc m) (suc n) = ack m (ack (suc m) n)

module ack-Props where
  lem∸ : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
  lem∸ z≤n = ≡.refl
  lem∸ (s≤s {m} {n} m≤n) = ≡.cong suc (lem∸ m≤n)

  -- n >= m → m + (n ∸ m) ≡ n
  -- n >= m → ∃ k → n ≡ m + k
  -- ∃ k → n ≡ m + k → m + (n ∸ m) ≡ n
  -- ∀ k → n ≡ m + k → m + (n ∸ m) ≡ n
  -- ∀ k → m + ((m + k) ∸ m) ≡ m + k
  -- ∀ k → m + k ≡ m + k

  -- 3 ≤ x → P x → ∃ λ k → P (3 + k)

  open InflModule

  fold1+-inflT< : ∀ {z} → InflT< (fold (suc z))
  fold1+-inflT<     _      {zero} = s≤s z≤n
  fold1+-inflT< {z} {f} finfl< {suc x} =
     2 + x                ≤⟨ s≤s (fold1+-inflT< {z} {f} finfl< {x}) ⟩
     1 + fold (suc z) f x ≤⟨ finfl< ⟩
     f (fold (suc z) f x) ≡⟨ ≡.refl ⟩
     fold (suc z) f (1 + x)
   ∎
     where open ≤-Reasoning

  Mon : (f : ℕ → ℕ) → Set
  Mon f = ∀ {x y} → x ≤ y → f x ≤ f y
  open InflModule


  ℕ-ind : ∀ (P : ℕ → Set) → P zero → (∀ {n} → P n → P (suc n)) → ∀ {n} → P n
  ℕ-ind P P0 PS {zero} = P0
  ℕ-ind P P0 PS {suc n} = PS (ℕ-ind P P0 PS)

  open fold-Props
  fold-infl< : ∀ {f g} → Infl< f → InflT< g → ∀ {n} → Infl< (fold f g n)
  fold-infl< {f} {g} inflf< inflTg< {n} = ℕ-ind (Infl< ∘ fold f g) inflf< inflTg< {n}

  fold-mon : ∀ {f} (fmon : Mon f) (finfl< : Infl< f) {z} → Mon (fold z f)
  fold-mon fmon finfl< {_} {y = 0} z≤n = ℕ≤.refl
  fold-mon {f} fmon finfl< {z} {y = suc n} z≤n = z ≤⟨ ≤-step ℕ≤.refl ⟩
                                              suc z ≤⟨ nest-infl< f finfl< n {z} ⟩
                                              fold z f (suc n) ≡⟨ ≡.refl ⟩
                                              fold z f (suc n) ∎
    where open ≤-Reasoning
  fold-mon fmon finfl< (s≤s m≤n) = fmon (fold-mon fmon finfl< m≤n)

  MonT : Endo (Endo ℕ) → Set
  MonT g = ∀ {f} → Mon f → Infl< f → Mon (g f)

  fold-mon' : ∀ {f g} → Mon f → Infl< f → MonT g → InflT< g → ∀ {n} → Mon (fold f g n)
  fold-mon' {f} {g} mon-f infl-f mont-g inflTg< {n} = go n where
    go : ∀ n → Mon (fold f g n)
    go zero    = mon-f
    go (suc n) = mont-g (go n) (fold-infl< infl-f inflTg< {n})


  --  +-fold : ∀ a b → a + b ≡ fold a suc b
  --  *-fold : ∀ a b → a * b ≡ fold 0 (_+_ a) b

  1≤1+a^b : ∀ a b → 1 ≤ (1 + a) ^ b
  1≤1+a^b a zero = s≤s z≤n
  1≤1+a^b a (suc b) = 1≤1+a^b a b +-mono z≤n

  1+a^-mon : ∀ {a} → Mon (_^_ (1 + a))
  1+a^-mon {a} (z≤n {b}) = 1≤1+a^b a b
  1+a^-mon {a} (s≤s {m} {n} m≤n)
     = (1 + a) ^ (1 + m)             ≡⟨ ≡.refl ⟩
       (1 + a) ^ m + a * (1 + a) ^ m ≤⟨ (1+a^-mon m≤n) +-mono ((a ∎) *-mono (1+a^-mon m≤n)) ⟩
       (1 + a) ^ n + a * (1 + a) ^ n ≡⟨ ≡.refl ⟩
       (1 + a) ^ (1 + n) ∎
    where open ≤-Reasoning

  postulate
    ↑3+ : ∀ a n b → a ↑⟨ 3 + n ⟩ b ≡ fold (_^_ a) (fold 1) n b
    -- mon↑3+'' : ∀ a b → Mon (λ n → fold (_^_ a) (fold 1) n b)

    mon↑3+' : ∀ b → Mon (λ n → fold (_^_ 2) (fold 1) n (3 + b))
  -- mon↑3+' b = {!!}

  mon↑3+ : ∀ b → Mon (λ n → 2 ↑⟨ 3 + n ⟩ (3 + b))
  mon↑3+ b {m} {n} rewrite ↑3+ 2 m (3 + b) | ↑3+ 2 n (3 + b) = mon↑3+' b

  lem2^3 : ∀ n → 2 ^ 3 ≤ 2 ^ (3 + n)
  lem2^3 n = 1+a^-mon {1} {3} {3 + n} (s≤s (s≤s (s≤s z≤n)))

  open ↑-Props
  lem>=3 : ∀ m n → 3 ≤ 2 ↑⟨ 3 + m ⟩ (3 + n)
  lem>=3 m n = 3 ≤⟨ s≤s (s≤s (s≤s z≤n)) ⟩
               2 ↑⟨ 3 ⟩ 3 ≡⟨ ↑₃-^ 2 3 ⟩
               2 ^ 3 ≤⟨ lem2^3 n ⟩
               2 ^ (3 + n) ≡⟨ ≡.sym (↑₃-^ 2 (3 + n)) ⟩
               2 ↑⟨ 3 ⟩ (3 + n) ≤⟨ mon↑3+ n z≤n ⟩
               2 ↑⟨ 3 + m ⟩ (3 + n) ∎
    where open ≤-Reasoning

  2* = _*_ 2

  -- fold 2* n 1 ≡ 2 ^ n

  -- nest-* : ∀ m n → nest (m * n) f ≗ nest m (nest n f)

  nest-2* : ∀ m n → nest (m * n) (fold 1) 2* ≡ nest m (nest n (fold 1)) 2*
  nest-2* m n = nest-Properties.nest-* (fold 1) m n 2*

{-
  lem3≤ : ∀ n → 3 ≤ fold 2* (fold 1) n 2
  lem3≤ 0 = s≤s (s≤s (s≤s z≤n))
    where open ≤-Reasoning
  lem3≤ (suc n) = 
    3 ≤⟨ {!!} ⟩
    fold 2* f1 (1 + n) 2 ∎
    where open ≤-Reasoning
          f1 = fold 1

  lem3≤' : ∀ n → 3 ≤ fold 2* (fold 1) n 3
  lem3≤' 0 = s≤s (s≤s (s≤s z≤n))
    where open ≤-Reasoning
  lem3≤' (suc n) = 
    3 ≤⟨ lem3≤ n ⟩
    fold 2* (fold 1) n 2 ≡⟨ ≡.refl ⟩
    fold 2* (fold 1) n (fold 2* (fold 1) 3 1) ≡⟨ {!!} ⟩
{- ≡⟨ nest-Properties.nest-* {!2*!} {!!} {!!} {!!} ⟩
    fold 2* (fold 1) (3 * n) 1 ≡⟨ {!!} ⟩
-}
    fold 1 (fold 2* (fold 1) n) 3 ≡⟨ ≡.refl ⟩
    fold 2* (fold 1) (1 + n) 3 ∎
    where open ≤-Reasoning
-}
---

{-
fold 2* (fold 1) (3 * n) 1 ≤

fold 2* (fold 1) n (fold 2* (fold 1) n (fold 2* (fold 1) n 1)) ≤

fold 1 (fold 2* (fold 1) n) 3 ≤
fold 2* (fold 1) (1 + n) 3
-}

  lem>=3'' : ∀ m n → 3 ≤ 2 ↑⟨ suc m ⟩ (3 + n)
  lem>=3'' zero n = s≤s (s≤s (s≤s z≤n))
  lem>=3'' (suc zero) n rewrite ↑₂-* 2 (3 + n) = s≤s (s≤s (s≤s z≤n))
  lem>=3'' (suc (suc m)) n = lem>=3 m n

  lem2221 : ∀ m → 2 ≡ 2 ↑⟨ 2 + m ⟩ 1
  lem2221 zero = ≡.refl
  lem2221 (suc m) = lem2221 m

  lem4212 : ∀ m → 4 ≡ 2 ↑⟨ 1 + m ⟩ 2
  lem4212 zero = ≡.refl
  lem4212 (suc m) = 4                            ≡⟨ lem4212 m ⟩
                    2 ↑⟨ 1 + m ⟩ 2               ≡⟨ ≡.cong (_↑⟨_⟩_ 2 (1 + m)) (lem2221 m) ⟩
                    2 ↑⟨ 1 + m ⟩ (2 ↑⟨ 2 + m ⟩ 1) ≡⟨ ≡.refl ⟩
                    2 ↑⟨ 2 + m ⟩ 2 ∎
    where open ≡-Reasoning

  ack-↑ : ∀ m n → 3 + ack m n ≡ 2 ↑⟨ m ⟩ (3 + n)
  ack-↑ zero n = ≡.refl
  ack-↑ (suc m) zero = 3 + ack (suc m) 0   ≡⟨ ack-↑ m 1 ⟩
                       2 ↑⟨ m ⟩ 4          ≡⟨ ≡.cong (_↑⟨_⟩_ 2 m) (lem4212 m) ⟩
                       2 ↑⟨ suc m ⟩ 3 ∎
    where open ≡-Reasoning
  ack-↑ (suc m) (suc n) = 3 + ack (suc m) (suc n)
                        ≡⟨ ≡.refl ⟩
                          3 + ack m (ack (suc m) n)
                        ≡⟨ ≡.refl ⟩
                          3 + ack m ((3 + ack (suc m) n) ∸ 3)
                        ≡⟨ ≡.cong (λ x → 3 + ack m (x ∸ 3)) (ack-↑ (suc m) n) ⟩
                           3 + ack m (2 ↑⟨ suc m ⟩ (3 + n) ∸ 3)
                        ≡⟨ ack-↑ m (2 ↑⟨ suc m ⟩ (3 + n) ∸ 3) ⟩
                           2 ↑⟨ m ⟩ (3 + (2 ↑⟨ suc m ⟩ (3 + n) ∸ 3))
                        ≡⟨ ≡.cong (λ x → 2 ↑⟨ m ⟩ x) (lem∸ (lem>=3'' m n)) ⟩
                           2 ↑⟨ m ⟩ (2 ↑⟨ suc m ⟩ (3 + n))
                        ≡⟨ ≡.refl ⟩
                          2 ↑⟨ suc m ⟩ (4 + n) ∎ 
    where open ≡-Reasoning

  postulate
    1+a^-infl< : ∀ {a}  → Infl< (_^_ (1 + a))

  --  2+a*1+b-infl< : ∀ a → Infl< (λ x → (2 + a) * (1 + x))
  -- ∀ a b → b < (2 + a) * b
  -- fold-a*-fold1 : ∀ {n a} → Infl< (_↑2+⟨_⟩_ (2 + a) n)
  fold-a^-fold1 : ∀ {n a} → Infl< (fold (_^_ (1 + a)) (fold 1) n)
  fold-a^-fold1 {n} = fold-infl< 1+a^-infl< fold1+-inflT< {n}

  ↑3+-mon : ∀ a n → Mon (fold (_^_ (1 + a)) (fold 1) n)
  ↑3+-mon a n = fold-mon' 1+a^-mon 1+a^-infl< (λ η₁ η₂ → fold-mon η₁ η₂) fold1+-inflT< {n}

{-
  open ↑-Props

  -*⟨1+n⟩-infl : ∀ n → Infl (_*_ (1 + n))
  -*⟨1+n⟩-infl n = {!!}

  lem121 : ∀ a b → b < (1 + a) ↑⟨ 2 ⟩ (1 + b)
  lem121 a b rewrite ↑₂-* (1 + a) (1 + b)
     = 1 + b
              ≤⟨ m≤m+n _ _ ⟩
       (1 + a) * (1 + b)
              ≡⟨ ℕ°.*-comm (1 + a) (1 + b) ⟩
       (1 + b) * (1 + a)
     ∎
     where open ≤-Reasoning

  -- ∀ a b → b < (2 + a) * b
  lem222 : ∀ a b → b < (2 + a) ↑⟨ 2 ⟩ (2 + b)
  lem222 a b rewrite ↑₂-* (2 + a) (2 + b)
     = 1 + b
              ≤⟨ suc-infl ⟩
       2 + b
              ≤⟨ m≤m+n _ _ ⟩
       (2 + a) * (2 + b)
              ≡⟨ ℕ°.*-comm (2 + a) (2 + b) ⟩
       (2 + b) * (2 + a)
     ∎
     where open ≤-Reasoning
-}
{-
  open fold-Props

  module Foo a where
    f = λ n b → (2 + a) ↑2+⟨ n ⟩ b
    f-lem : ∀ n → f (suc n) ≗ fold 1 (f n)
    f-lem n x = ≡.refl

    f2 = λ n b → (2 + a) ↑2+⟨ n ⟩ (2 + b)
    f2-lem : ∀ n → f2 (suc n) ≗ fold 1 (f2 n)
    f2-lem n x = {!!}

  -- b < (1 + a) * (1 + b)

 -- nest-infl< : ∀ f (finfl< : Infl< f) n → Infl< (nest (suc n) f)
  infl3< : ∀ a n → Infl< (λ b → (1 + a) ↑2+⟨ n ⟩ (1 + b))
  infl3< a zero {b} = lem121 a b
  infl3< a (suc n) {b}
    = 1 + b
 --  fold1-infl< : ∀ f → Infl< f → ∀ x → x < fold 1 f x
            ≤⟨ {!fold1f2-infl< {_}!} ⟩
      fold 1 f1 b
            ≤⟨ {!!} ⟩
{-
            ≤⟨ fold1-infl< (f 0) (λ {x} → {!infl3< a n {x}!}) {{!!}} ⟩
      {!!}
            ≤⟨ {!!} ⟩
-}
{-
      1 + b
      (2 + a) ↑2+⟨ n ⟩ (2 + b)
            ≤⟨ {!nest-infl< (λ b → (2 + a) ↑2+⟨ n ⟩ b) ? b {(2 + a) ↑2+⟨ n ⟩ (2 + b)}!} ⟩
      fold (f 0 1) (f 0) (1 + b)
            ≤⟨ {!ℕ≤.reflexive (≡.cong (λ g → g 1) (nest-Properties.nest-+ (f 0) 1 (1 + b)))!} ⟩
-}
      fold 1 (f 0) (1 + b)
            ≡⟨ ≡.refl ⟩
      f 1 (1 + b)
            ≡⟨ ≡.refl ⟩
      (1 + a) ↑2+⟨ suc n ⟩ (1 + b)
    ∎

     where
       f = λ k b → (1 + a) ↑2+⟨ k + n ⟩ b
       f1 = f 0 ∘ suc

       -- fold1f2-infl< : Infl< (fold 1 f2)
       -- fold1f2-infl< = fold1-infl< f2 {!(λ b → infl3< a n b ?)!}

       fold1f1-infl<' : Infl< (fold 1 f1)
       fold1f1-infl<' = {!fold1+1-infl< (f 0) {!infl3< a n!}!}
       lem : ∀ x → f 0 (1 + x) < f 0 (f 0 x)
       lem x = {!!}
       postulate
         finfl : Infl< (f 0)
       open ≤-Reasoning
-}

_⇑⟨_,_⟩_ : (a n k b : ℕ) → ℕ
a ⇑⟨ n , k ⟩ b = fold k f n
  module M⇑ where 
    f : ℕ → ℕ
    f x = a ↑⟨ 2 + x ⟩ b

module ⇑-Props where
  _⇑′⟨_,_⟩_ : (a n k b : ℕ) → ℕ
  a ⇑′⟨ n₀ , k ⟩ b = g n₀
    module M⇑′ where
      h : ℕ → ℕ
      h x = a ↑⟨ 2 + x ⟩ b

      g : ℕ → ℕ
      g 0       = k
      g (suc n) = h (g n)

      g-nest : ∀ n → g n ≡ h $⟨ n ⟩ k
      g-nest zero = ≡.refl
      g-nest (suc n) rewrite g-nest n = ≡.refl

  ⇑₀ : ∀ a k b → a ⇑⟨ 0 , k ⟩ b ≡ k
  ⇑₀ _ _ _ = ≡.refl

  ⇑₁ : ∀ a k b → a ⇑⟨ 1 , k ⟩ b ≡ a ↑⟨ 2 + k ⟩ b
  ⇑₁ _ _ _ = ≡.refl

  ⇑-⇑′ : ∀ a n k b → a ⇑⟨ n , k ⟩ b ≡ a ⇑′⟨ n , k ⟩ b
  ⇑-⇑′ a n k b rewrite M⇑′.g-nest a n k b n = ≡.refl

-- https://en.wikipedia.org/wiki/Graham%27s_number
Graham's-number : ℕ
Graham's-number = 3 ⇑⟨ 64 , 4 ⟩ 3
  -- = (f∘⁶⁴…∘f)4
  -- where f x = 3 ↑⟨ 2 + x ⟩ 3

{-
module GeneralisedArithmetic {a} {A : Set a} (0# : A) (1+ : A → A) where

  1# : A
  1# = 1+ 0#

  open Data.Nat.GeneralisedArithmetic 0# 1+ public

  exp : (* : A → A → A) → (ℕ → A → A)
  exp _*_ n b = fold 1# (λ s → b * s) n
-}
  -- hyperop a n b = fold exp

module == where
  _≈_ : (m n : ℕ) → Set
  m ≈ n = T (m == n)

  subst : ∀ {ℓ} → Substitutive _≈_ ℓ
  subst _ {zero}  {zero}  _  = id
  subst P {suc _} {suc _} p  = subst (P ∘ suc) p
  subst _ {zero}  {suc _} ()
  subst _ {suc _} {zero}  ()

  sound : ∀ m n → T (m == n) → m ≡ n
  sound m n p = subst (_≡_ m) p ≡.refl

  refl : Reflexive _≈_
  refl {zero}  = _
  refl {suc n} = refl {n}

  sym : Symmetric _≈_
  sym {m} {n} eq rewrite sound m n eq = refl {n}

  trans : Transitive _≈_
  trans {m} {n} {o} m≈n n≈o rewrite sound m n m≈n | sound n o n≈o = refl {o}

  setoid : Setoid _ _
  setoid = record { Carrier = ℕ; _≈_ = _≈_
                  ; isEquivalence =
                      record { refl = λ {x} → refl {x}
                             ; sym = λ {x} {y} → sym {x} {y}
                             ; trans = λ {x} {y} {z} → trans {x} {y} {z} } }

  open Setoid setoid public hiding (refl; sym; trans; _≈_)

{-
data _`≤?`_↝_ : (m n : ℕ) → Dec (m ≤ n) → Set where
  z≤?n     : ∀ {n} → zero `≤?` n ↝ yes z≤n
  s≤?z     : ∀ {m} → suc m `≤?` zero ↝ no λ()
  s≤?s-yes : ∀ {m n m≤n} → m `≤?` n ↝ yes m≤n → suc m `≤?` suc n ↝ yes (s≤s m≤n)
  s≤?s-no  : ∀ {m n m≰n} → m `≤?` n ↝ no m≰n → suc m `≤?` suc n ↝ no (m≰n ∘ ≤-pred)

`≤?`-complete : ∀ m n → m `≤?` n ↝ (m ≤? n)
`≤?`-complete zero n = z≤?n
`≤?`-complete (suc n) zero = {!s≤?z!}
`≤?`-complete (suc m) (suc n) with m ≤? n | `≤?`-complete m n
... | yes q | r = s≤?s-yes r
... | no q  | r = s≤?s-no {!!}
-}

_<=_ : (x y : ℕ) → Bool
zero   <= _      = true
suc _  <= zero   = false
suc m  <= suc n  = m <= n

module <= where
  sound : ∀ m n → T (m <= n) → m ≤ n
  sound zero    _       _  = z≤n
  sound (suc m) (suc n) p  = s≤s (sound m n p)
  sound (suc m) zero    ()

  complete : ∀ {m n} → m ≤ n → T (m <= n)
  complete z≤n       = _
  complete (s≤s m≤n) = complete m≤n

¬≤ : ∀ {m n} → ¬(m < n) → n ≤ m
¬≤ {m} {n} p with ℕcmp.compare m n
... | tri< m<n _ _   = ⊥-elim (p m<n)
... | tri≈ _ eq _    = ℕ≤.reflexive (≡.sym eq)
... | tri> _ _ 1+n≤m = ≤-pred (Props.≤-steps 1 1+n≤m)
