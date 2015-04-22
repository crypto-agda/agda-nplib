open import Data.Nat.NP
open import Data.Nat.Properties as Props
open import Data.Product
open import Relation.Binary.PropositionalEquality.NP

module Data.Nat.Distance where

dist : ℕ → ℕ → ℕ
dist zero    y       = y
dist x       zero    = x
dist (suc x) (suc y) = dist x y

dist-refl : ∀ x → dist x x ≡ 0
dist-refl zero = idp
dist-refl (suc x) rewrite dist-refl x = idp

dist-0≡id : ∀ x → dist 0 x ≡ x
dist-0≡id _ = idp

dist-x-x+y≡y : ∀ x y → dist x (x + y) ≡ y
dist-x-x+y≡y zero    y = idp
dist-x-x+y≡y (suc x) y = dist-x-x+y≡y x y

dist-comm : ∀ x y → dist x y ≡ dist y x
dist-comm zero zero = idp
dist-comm zero (suc y) = idp
dist-comm (suc x) zero = idp
dist-comm (suc x) (suc y) = dist-comm x y

dist-x+ : ∀ x y z → dist (x + y) (x + z) ≡ dist y z
dist-x+ zero    y z = idp
dist-x+ (suc x) y z = dist-x+ x y z

dist-2* : ∀ x y → dist (2* x) (2* y) ≡ 2* dist x y
dist-2* zero y = idp
dist-2* (suc x) zero = idp
dist-2* (suc x) (suc y) rewrite +-assoc-comm x 1 x | +-assoc-comm y 1 y = dist-2* x y

dist-asym-def : ∀ {x y} → x ≤ y → x + dist x y ≡ y
dist-asym-def z≤n = idp
dist-asym-def (s≤s pf) = ap suc (dist-asym-def pf)

dist-sym-wlog : ∀ (f : ℕ → ℕ) → (∀ x k → dist (f x) (f (x + k)) ≡ f k) → ∀ x y → dist (f x) (f y) ≡ f (dist x y)
dist-sym-wlog f pf x y with compare x y
dist-sym-wlog f pf x .(suc (x + k)) | less .x k with pf x (suc k)
... | q rewrite +-assoc-comm x 1 k | q | ! +-assoc-comm x 1 k | dist-x-x+y≡y x (suc k) = idp
dist-sym-wlog f pf .y y | equal .y with pf y 0
... | q rewrite ℕ°.+-comm y 0 | dist-refl y = q
dist-sym-wlog f pf .(suc (y + k)) y | greater .y k with pf y (suc k)
... | q rewrite +-assoc-comm 1 y k | dist-comm (y + suc k) y | dist-x-x+y≡y y (suc k) | dist-comm (f (y + suc k)) (f y) = q

dist-x* : ∀ x y z → dist (x * y) (x * z) ≡ x * dist y z
dist-x* x = dist-sym-wlog (_*_ x) pf
  where pf : ∀ a k → dist (x * a) (x * (a + k)) ≡ x * k
        pf a k rewrite proj₁ ℕ°.distrib x a k = dist-x-x+y≡y (x * a) _

dist-2^* : ∀ x y z → dist ⟨2^ x * y ⟩ ⟨2^ x * z ⟩ ≡ ⟨2^ x * dist y z ⟩
dist-2^* x = dist-sym-wlog (2^⟨ x ⟩*) pf
  where pf : ∀ a k → dist ⟨2^ x * a ⟩ ⟨2^ x * (a + k) ⟩ ≡ ⟨2^ x * k ⟩
        pf a k rewrite 2^*-distrib x a k = dist-x-x+y≡y ⟨2^ x * a ⟩ ⟨2^ x * k ⟩

dist-bounded : ∀ {x y f} → x ≤ f → y ≤ f → dist x y ≤ f
dist-bounded z≤n       y≤f = y≤f
dist-bounded (s≤s x≤f) z≤n = s≤s x≤f
dist-bounded (s≤s x≤f) (s≤s y≤f) = ≤-step (dist-bounded x≤f y≤f)

-- Triangular inequality
dist-sum : ∀ x y z → dist x z ≤ dist x y + dist y z
dist-sum zero    zero    z       = ℕ≤.refl
dist-sum zero    (suc y) zero    = z≤n
dist-sum zero    (suc y) (suc z) = s≤s (dist-sum zero y z)
dist-sum (suc x) zero    zero    = s≤s (ℕ≤.reflexive (ℕ°.+-comm 0 x))
dist-sum (suc x) (suc y) zero
  rewrite ℕ°.+-comm (dist x y) (suc y)
        | dist-comm x y = s≤s (dist-sum zero y x)
dist-sum (suc x) zero    (suc z) = dist-sum x zero z
                                ∙≤ ℕ≤.reflexive (ap₂ _+_ (dist-comm x 0) idp)
                                ∙≤ ≤-step (ℕ≤.refl {x} +-mono ≤-step ℕ≤.refl)
dist-sum (suc x) (suc y) (suc z) = dist-sum x y z

dist≡0 : ∀ x y → dist x y ≡ 0 → x ≡ y
dist≡0 zero zero d≡0 = refl
dist≡0 zero (suc y) ()
dist≡0 (suc x) zero ()
dist≡0 (suc x) (suc y) d≡0 = ap suc (dist≡0 x y d≡0)

∸-dist : ∀ x y → y ≤ x → x ∸ y ≡ dist x y
∸-dist x .0 z≤n = ! dist-comm x 0
∸-dist ._ ._ (s≤s y≤x) = ∸-dist _ _ y≤x

{-
post--ulate
  dist-≤     : ∀ x y → dist x y ≤ x
  dist-mono₁ : ∀ x y z t → x ≤ y → dist z t ≤ dist (x + z) (y + t)
-}

-- Haskell
-- let dist x y = abs (x - y)
-- quickCheck (forAll (replicateM 3 (choose (0,100))) (\ [x,y,z] -> dist (x * y) (x * z) == x * dist y z))
