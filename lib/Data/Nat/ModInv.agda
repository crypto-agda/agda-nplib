{-# OPTIONS --without-K #-}
open import Function
open import Data.Zero
open import Data.Nat.NP
open import Data.Nat.Properties
-- open import Data.Nat.DivMod
open import Data.Nat.DivMod.NP
open import Data.Nat.Primality.NP
open import Data.Nat.Coprimality
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Data.Product.NP
open import Data.Fin.NP using (Fin; Fin▹ℕ; zero; suc; Fin▹ℕ<)
open import Relation.Nullary.Decidable hiding (⌊_⌋)
open import Relation.Binary.PropositionalEquality.NP

module Data.Nat.ModInv (q : ℕ) (q-prime : Prime q) where

prime≢0 : ∀ {x} → Prime x → False (x ≟ 0)
prime≢0 {zero}  ()
prime≢0 {suc _} _ = _

q≢0 : False (q ≟ 0)
q≢0 = prime≢0 q-prime

1<q : 1 < q
1<q = prime-≥2 q-prime

0<q : 0 < q
0<q = ℕ≤.trans (s≤s z≤n) 1<q

gcd≡1 : ∀ n d → 0 < n → n < q → GCD n q d → d ≡ 1
gcd≡1 n d 0<n n<q g
  = GCD.unique g (GCD.sym (coprime-gcd (prime⇒coprime q q-prime n 0<n n<q)))

⌊_⌋ : ℕ → ℕ
⌊ x ⌋ = x modℕ q

_/q : ℕ → ℕ
x /q = x div q

∣≢→< : ∀ d q (q≢0 : False (q ≟ 0)) → d ∣ q → d ≢ q → d < q
∣≢→< d zero () d∣q d≢q
∣≢→< d (suc q-1) q≢0 d∣q d≢q = ≤≢→< (∣⇒≤ d∣q) d≢q

open ≡-Reasoning

divMod-prop : ∀ x → x ≡ ⌊ x ⌋ + x /q * q
divMod-prop x = divModPropℕ x q

mod<q : ∀ x → ⌊ x ⌋ < q
mod<q x = modℕ<divisor x q {q≢0}

≥d*q : ∀ x → x ≥ (x /q) * q
≥d*q x = ≡+-≥ x ⌊ x ⌋ (x /q * q) (divMod-prop x)

q/q≡1 : q /q ≡ 1
q/q≡1 = d/d≡1 q {q≢0}

mod-prop : ∀ x → ⌊ x ⌋ ≡ x ∸ (x /q) * q
mod-prop x = modℕ-prop x {q}

q-mod-q : ⌊ q ⌋ ≡ 0
q-mod-q = mod-prop q ∙
  (q ∸ q /q * q ≡⟨ ap (λ z → q ∸ z * q) q/q≡1 ⟩
   q ∸ 1 * q    ≡⟨ ap (_∸_ q) (ℕ°.+-comm q 0) ⟩
   q ∸ q        ≡⟨ n∸n≡0 q ⟩
   0 ∎)

0-mod : ⌊ 0 ⌋ ≡ 0
0-mod = mod-prop 0 ∙ 0∸n≡0 (0 /q * q)

{-
q∸-mod : ∀ {x} → q ≥ x → ⌊ q ∸ x ⌋ ≡ q ∸ ⌊ x ⌋
q∸-mod p = modℕ-s∸ {!!} {!p!}
-}

-- q+-mod : ∀ {x} → ⌊ q + x ⌋ ≡ ⌊ x ⌋
-- q+-mod = {!!}

∸q-mod : ∀ {x} → x ≥ q → ⌊ x ∸ q ⌋ ≡ ⌊ x ⌋
∸q-mod = modℕ-∸s

∸-*q-mod : ∀ x y → x ≥ y * q → ⌊ x ∸ y * q ⌋ ≡ ⌊ x ⌋
∸-*q-mod x zero H = idp
∸-*q-mod x (suc y) H =
  ⌊ x ∸ (q + y * q) ⌋ ≡⟨ ap ⌊_⌋ (! ∸-assoc-+ x q _) ⟩
  ⌊ x ∸ q ∸ y * q ⌋ ≡⟨ ∸-*q-mod _ y (+≤→≤∸ q H) ⟩
  ⌊ x ∸ q ⌋ ≡⟨ ∸q-mod (+≤ q H) ⟩
  ⌊ x ⌋ ∎

mod-mod : ∀ x → ⌊ ⌊ x ⌋ ⌋ ≡ ⌊ x ⌋
mod-mod x = ⌊ ⌊ x ⌋ ⌋ ≡⟨ ap ⌊_⌋ (mod-prop x) ⟩
            ⌊ x ∸ x /q * q ⌋ ≡⟨ ∸-*q-mod x (x /q) (≥d*q x) ⟩
            ⌊ x ⌋ ∎

<-/q-0 : ∀ {x} → x < q → x /q ≡ 0
<-/q-0 = div<≡0

<-mod : ∀ x → x < q → ⌊ x ⌋ ≡ x
<-mod x x<q = mod-prop x ∙ ap (λ z → x ∸ z * q) (<-/q-0 x<q)

k+-mod : ∀ k {x} → ⌊ k + ⌊ x ⌋ ⌋ ≡ ⌊ k + x ⌋
k+-mod k {x} =
  ⌊ k + ⌊ x ⌋ ⌋ ≡⟨ ap (λ z → ⌊ k + z ⌋) (mod-prop _) ⟩
  ⌊ k + (x ∸ x /q * q) ⌋ ≡⟨ ap ⌊_⌋ (! +-∸-assoc k (≥d*q x)) ⟩
  ⌊ k + x ∸ x /q * q ⌋ ≡⟨ ∸-*q-mod (k + x) (x /q)
                           (let open ≤-Reasoning in
                            x /q * q ≤⟨ ≥d*q x ⟩
                            x ≤⟨ ≤-steps′ k ⟩
                            ℕ≤.reflexive (ℕ°.+-comm x k)) ⟩
  ⌊ k + x ⌋ ∎

+k-mod : ∀ {x} k → ⌊ ⌊ x ⌋ + k ⌋ ≡ ⌊ x + k ⌋
+k-mod {x} k =
  ⌊ ⌊ x ⌋ + k ⌋  ≡⟨ ap ⌊_⌋ (ℕ°.+-comm ⌊ x ⌋ k) ⟩
  ⌊ k + ⌊ x ⌋ ⌋  ≡⟨ k+-mod k ⟩
  ⌊ k + x ⌋      ≡⟨ ap ⌊_⌋ (ℕ°.+-comm k x) ⟩
  ⌊ x + k ⌋      ∎

+-mod : ∀ x y → ⌊ ⌊ x ⌋ + ⌊ y ⌋ ⌋ ≡ ⌊ x + y ⌋
+-mod x y = k+-mod ⌊ x ⌋ ∙ +k-mod y

suc-mod : ∀ x → ⌊ suc ⌊ x ⌋ ⌋ ≡ ⌊ suc x ⌋
suc-mod x = k+-mod 1

1-mod : ⌊ 1 ⌋ ≡ 1
1-mod = 1-modℕ {q} 1<q 

k*-mod : ∀ k {x} → ⌊ k * ⌊ x ⌋ ⌋ ≡ ⌊ k * x ⌋
k*-mod zero = idp
k*-mod (suc k) {x} =
  ⌊ ⌊ x ⌋ +   k * ⌊ x ⌋   ⌋ ≡⟨ +k-mod (k * ⌊ x ⌋) ⟩
  ⌊   x   +   k * ⌊ x ⌋   ⌋ ≡⟨ ! k+-mod x ⟩
  ⌊   x   + ⌊ k * ⌊ x ⌋ ⌋ ⌋ ≡⟨ ap (λ z → ⌊ x + z ⌋) (k*-mod k {x}) ⟩
  ⌊   x   + ⌊ k *   x   ⌋ ⌋ ≡⟨ k+-mod x ⟩
  ⌊   x   +   k *   x     ⌋ ∎

*k-mod : ∀ {x} k → ⌊ ⌊ x ⌋ * k ⌋ ≡ ⌊ x * k ⌋
*k-mod {x} k = 
  ⌊ ⌊ x ⌋ * k ⌋  ≡⟨ ap ⌊_⌋ (ℕ°.*-comm ⌊ x ⌋ k) ⟩
  ⌊ k * ⌊ x ⌋ ⌋  ≡⟨ k*-mod k ⟩
  ⌊ k * x ⌋      ≡⟨ ap ⌊_⌋ (ℕ°.*-comm k x) ⟩
  ⌊ x * k ⌋      ∎

*-mod : ∀ x y → ⌊ ⌊ x ⌋ * ⌊ y ⌋ ⌋ ≡ ⌊ x * y ⌋
*-mod x y = k*-mod ⌊ x ⌋ ∙ *k-mod y

nq-mod-q : ∀ n → ⌊ n * q ⌋ ≡ 0
nq-mod-q n = 
  ⌊ n * q ⌋     ≡⟨ ! k*-mod n {q} ⟩
  ⌊ n * ⌊ q ⌋ ⌋ ≡⟨ ap (⌊_⌋ ∘ _*_ n) q-mod-q ⟩
  ⌊ n * 0     ⌋ ≡⟨ ap ⌊_⌋ (ℕ°.*-comm n 0) ⟩
  ⌊ 0 ⌋         ≡⟨ 0-mod ⟩
  0             ∎

+q-mod : ∀ x → ⌊ x + q ⌋ ≡ ⌊ x ⌋
+q-mod x = 
  ⌊ x + q ⌋     ≡⟨ ! k+-mod x {q} ⟩
  ⌊ x + ⌊ q ⌋ ⌋ ≡⟨ ap (λ z → ⌊ x + z ⌋) q-mod-q ⟩
  ⌊ x + 0     ⌋ ≡⟨ ap ⌊_⌋ (ℕ°.+-comm x 0) ⟩
  ⌊ x ⌋         ∎

+nq-mod : ∀ x n → ⌊ x + n * q ⌋ ≡ ⌊ x ⌋
+nq-mod x n =
  ⌊ x + n * q ⌋     ≡⟨ ! k+-mod x {n * q} ⟩
  ⌊ x + ⌊ n * q ⌋ ⌋ ≡⟨ ap (λ z → ⌊ x + z ⌋) (nq-mod-q n) ⟩
  ⌊ x + 0         ⌋ ≡⟨ ap ⌊_⌋ (ℕ°.+-comm x 0) ⟩
  ⌊ x ⌋             ∎

{-
∸k-mod : ∀ k {x} → ⌊ ⌊ x ⌋ ∸ k ⌋ ≡ ⌊ x ∸ k ⌋
∸k-mod k {x} = {!!}

k∸-mod : ∀ k {x} → ⌊ k ∸ ⌊ x ⌋ ⌋ ≡ ⌊ k ∸ x ⌋
k∸-mod k {x} =
  ⌊ k ∸ ⌊ x ⌋ ⌋ ≡⟨ {!!} ⟩
  ⌊ k ∸ (x ∸ (x /q) * q) ⌋ ≡⟨ {!!} ⟩
  ⌊ k ∸ (x ∸ (x /q) * q) ⌋ ≡⟨ {!!} ⟩
  ⌊ k ∸ x     ⌋ ∎
-}

+-*q-mod : ∀ d y → ⌊ d + y * q ⌋ ≡ ⌊ d ⌋
+-*q-mod d y =
  ⌊ d + y * q ⌋
    ≡⟨ ! k+-mod d ⟩
  ⌊ d + ⌊ y * q ⌋ ⌋
    ≡⟨ ap (λ x → ⌊ d + x ⌋) (! k*-mod y) ⟩
  ⌊ d + ⌊ y * ⌊ q ⌋ ⌋ ⌋
    ≡⟨ ap (λ x → ⌊ d + ⌊ y * x ⌋ ⌋) q-mod-q ⟩
  ⌊ d + ⌊ y * 0 ⌋ ⌋
    ≡⟨ ap (λ x → ⌊ d + ⌊ x ⌋ ⌋) (ℕ°.*-comm y 0) ⟩
  ⌊ d + ⌊ 0 ⌋ ⌋
    ≡⟨ ap (λ x → ⌊ d + x ⌋) 0-mod ⟩
  ⌊ d + 0 ⌋
    ≡⟨ ap ⌊_⌋ (ℕ°.+-comm _ 0) ⟩
  ⌊ d ⌋ ∎

1/ : ℕ → ℕ
1/ n with Bézout.lemma q n
1/ n | Bézout.result d g (Bézout.+- x y eq) = STUCK q n x y where postulate STUCK : (q n x y : ℕ) → ℕ -- q ∸ y
1/ n | Bézout.result d g (Bézout.-+ x y eq) = y

gcd≢q : ∀ n q d → n ≢ 0 → n < q → GCD n q d → d ≢ q
gcd≢q zero      q  _ n≢0 n<q g _    = 𝟘-elim (n≢0 refl)
gcd≢q (suc n-1) q .q n≢0 n<q g refl = no-<-> n<q q<n
  where q<n = ∣≢→< q (suc n-1) _ (fst (GCD.commonDivisor g)) (<→≢ n<q ∘ !_)

blah' : ∀ x → suc x ∸ x ≡ 1
blah' zero = refl
blah' (suc x) = blah' x

blah : ∀ x → 0 < x → x ∸ (x ∸ 1) ≡ 1
blah zero ()
blah (suc x) p = blah' x

1<q+ : ∀ x → 1 < q + x
1<q+ x = ℕ≤.trans (prime-≥2 q-prime) (≤-steps′ {q} x)

{-
*q-∸-mod : ∀ x y → 0 < y → y < x * q → ⌊ x * q ∸ y ⌋ ≡ q ∸ ⌊ y ⌋
*q-∸-mod x y = modℕ-ns∸ {x} {y}
-}

{-
TODO remove n < q assumption


1/-prop : ∀ n → n ≢ 0 → n < q → ⌊ 1/ n * n ⌋ ≡ 1
1/-prop n n≢0 n<q with Bézout.lemma q n
1/-prop n n≢0 n<q | Bézout.result d g (Bézout.-+ x y eq) =
  ⌊ y * n     ⌋ ≡⟨ ap ⌊_⌋ (! eq) ⟩
  ⌊ d + x * q ⌋ ≡⟨ +-*q-mod d x ⟩
  ⌊ d         ⌋ ≡⟨ ap ⌊_⌋ (gcd≡1 n d (≢0⇒0< n n≢0) n<q (GCD.sym g)) ⟩
  ⌊ 1         ⌋ ≡⟨ 1-mod ⟩
  1 ∎
1/-prop n n≢0 n<q | Bézout.result d g (Bézout.+- zero y eq) = {!!}
1/-prop n n≢0 n<q | Bézout.result d g (Bézout.+- (suc x-1) y eq) =
  ⌊ (q ∸ y)   * n       ⌋ ≡⟨ ap ⌊_⌋ (*-distrib-∸ʳ n q y) ⟩
  ⌊ q * n ∸ y * n       ⌋ ≡⟨ ap ⌊_⌋ (ap (_∸_ (q * n)) (+-∸' d (y * n) (x * q) eq)) ⟩
  ⌊ q * n ∸ (x * q ∸ d) ⌋ ≡⟨ ap (λ z → ⌊ q * n ∸ (x * q ∸ z) ⌋) d≡1 ⟩
  ⌊ q * n ∸ (x * q ∸ 1) ⌋ ≡⟨ ap (λ z → ⌊ z ∸ (x * q ∸ 1) ⌋) (ℕ°.*-comm q n) ⟩
  ⌊ n * q ∸ (x * q ∸ 1) ⌋ ≡⟨ *q-∸-mod n _ {!!} xq∸1<nq ⟩
  q ∸ ⌊ x * q ∸ 1 ⌋ ≡⟨ ap (_∸_ q) (*q-∸-mod x _ (s≤s z≤n) (1<q+ (x-1 * q))) ⟩
  q ∸ (q ∸ ⌊ 1 ⌋) ≡⟨ ap (λ z → q ∸ (q ∸ z)) 1-mod ⟩
  q ∸ (q ∸ 1) ≡⟨ blah q 0<q ⟩
  {-
  ⌊ n * q ∸ (x * q ∸ 1) ⌋ ≡⟨ *q-∸-mod n _ {!+≤!} ⟩
  ⌊ x * q ∸ 1           ⌋ ≡⟨ *q-∸-mod x _ (+≤ 1 (ℕ≤.reflexive e)) ⟩
  ⌊ 1 ⌋                   ≡⟨ 1-mod ⟩
  -}
  1                       ∎
  where d≡1 = gcd≡1 n d (≢0⇒0< n n≢0) n<q (GCD.sym g)
        e   = ap₂ _+_ (! d≡1) idp ∙ eq
        x = suc x-1
        xq<nq+1 : x * q < n * q + 1
        xq<nq+1 = {!!}


        xq∸1<nq : x * q ∸ 1 < n * q
        xq∸1<nq = {!!}

1/-prop' : ∀ n → n ≢ 0 → n < q → ⌊ n * 1/ n ⌋ ≡ 1
1/-prop' n n≢0 n<q = ⌊ n * 1/ n ⌋ ≡⟨ ap ⌊_⌋ (ℕ°.*-comm n (1/ n)) ⟩
                     ⌊ 1/ n * n ⌋ ≡⟨ 1/-prop n n≢0 n<q ⟩
                     1            ∎
-}

-- -}
-- -}
-- -}
-- -}
-- -}
