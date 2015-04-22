module Data.Nat.DivMod.NP where

open import Data.Fin as Fin using (Fin; toℕ; #_)
import Data.Fin.Properties as FinP
open import Data.Product
open import Data.Nat.NP as Nat
open import Data.Nat.Properties as NatP
open import Data.Nat.Properties.Simple
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe.NP
  using (erase)
open import Relation.Binary

{-
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Explicits.FromAssocComm _+_ +-assoc +-comm
  renaming ( assoc-comm to +-assoc-comm )
-}

open NatP.SemiringSolver
open P.≡-Reasoning

infixl 7 _div_ -- _modℕ_ -- _mod_ -- _divMod_

-- A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

-- Integer division.

private

  div-helper : ℕ → ℕ → ℕ → ℕ → ℕ
  div-helper ack s zero    n       = ack
  div-helper ack s (suc d) zero    = div-helper (suc ack) s d s
  div-helper ack s (suc d) (suc n) = div-helper ack       s d n

  {-# BUILTIN NATDIVSUCAUX div-helper #-}

div-helper' : ℕ → ℕ → ℕ → ℕ
div-helper' s zero    n       = 0
div-helper' s (suc d) zero    = suc (div-helper' s d s)
div-helper' s (suc d) (suc n) =      div-helper' s d n

{-
div-helper-prop' : ∀ ack s d n → div-helper ack s d n ≡ div-helper' s d n + ack
div-helper-prop' ack s zero n = P.refl
div-helper-prop' ack s (suc d) zero = {!div-helper-prop' (suc ack) s d s!}
div-helper-prop' ack s (suc d) (suc n) = div-helper-prop' ack s d n
-}

div-helper-prop : ∀ ack s d n → div-helper ack s d n ≡ div-helper' s d n +ᵃ ack
div-helper-prop ack s zero n = P.refl
div-helper-prop ack s (suc d) zero = div-helper-prop (suc ack) s d s
div-helper-prop ack s (suc d) (suc n) = div-helper-prop ack s d n

_div_ : (dividend divisor : ℕ) → ℕ
(d div 0)     = 0
(d div suc s) = div-helper 0 s d s

-- The remainder after integer division.

private

  mod-helper : ℕ → ℕ → ℕ → ℕ → ℕ
  mod-helper ack s zero    n       = ack
  mod-helper ack s (suc d) zero    = mod-helper zero      s d s
  mod-helper ack s (suc d) (suc n) = mod-helper (suc ack) s d n

  {-# BUILTIN NATMODSUCAUX mod-helper #-}

  -- The remainder is not too large.

  mod-lemma : (ack d n : ℕ) →
              let s = ack + n in
              mod-helper ack s d n ≤ s

  mod-lemma ack zero n = m≤m+n ack n

  mod-lemma ack (suc d) zero = mod-lemma zero d (ack + 0)

  mod-lemma ack (suc d) (suc n) =
    P.subst (λ x → mod-helper (suc ack) x d n ≤ x)
            (P.sym (+-suc ack n))
            (mod-lemma (suc ack) d n)

  mod-helper-+ᵃ : ∀ ack {d n} → d ≤ n → mod-helper ack (ack +ᵃ n) d n ≡ d +ᵃ ack
  mod-helper-+ᵃ ack z≤n = P.refl
  mod-helper-+ᵃ ack (s≤s d≤n) = mod-helper-+ᵃ (suc ack) d≤n

  mod-helper0-+ᵃ : ∀ {d n} → d ≤ n → mod-helper 0 n d n ≡ d
  mod-helper0-+ᵃ d≤n = P.trans (mod-helper-+ᵃ 0 d≤n) (+ᵃ0-identity _)

  mod-helper-+ᵃ-∸-+ᵃ : ∀ ack {s d} → s ≤ d → mod-helper 0 (ack +ᵃ s) (d ∸ s) (ack +ᵃ s) ≡ mod-helper ack (ack +ᵃ s) (suc d) s
  mod-helper-+ᵃ-∸-+ᵃ ack z≤n = P.refl
  mod-helper-+ᵃ-∸-+ᵃ ack (s≤s p) = mod-helper-+ᵃ-∸-+ᵃ (suc ack) p

  _+ᵃ-mono_ : _+ᵃ_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  _+ᵃ-mono_ {x} {y} {u} {v} p q rewrite +ᵃ-+ x u | +ᵃ-+ y v = p +-mono q

{-
  mod-helper0-+ᵃ-id-+ᵃ : ∀ ack d s → d ≤ ack → mod-helper 0 (ack +ᵃ s) d (ack +ᵃ s) ≡ d
  mod-helper0-+ᵃ-id-+ᵃ ack d zero    p rewrite +ᵃ0-identity ack = mod-helper0-+ᵃ {d} {ack} p
  mod-helper0-+ᵃ-id-+ᵃ ack d (suc s) p = mod-helper0-+ᵃ-id-+ᵃ (suc ack) d s (≤-step p)

  mod-helper0-+ᵃ-id-+ᵃ' : ∀ k ack s → mod-helper 0 (k + ack +ᵃ s) (k +ᵃ s) (k + ack +ᵃ s) ≡ k +ᵃ s
  mod-helper0-+ᵃ-id-+ᵃ' k ack s = mod-helper0-+ᵃ-id-+ᵃ (k + ack) (k +ᵃ s) s {!!}
-}

  mod-helper0-+ᵃ-+ᵃ-+ᵃ : ∀ a k s → mod-helper 0 (a + k +ᵃ s) (a +ᵃ s) (a + k +ᵃ s) ≡ a +ᵃ s
  mod-helper0-+ᵃ-+ᵃ-+ᵃ a k zero    rewrite +ᵃ0-identity a | +ᵃ0-identity (a + k)
                                        = mod-helper0-+ᵃ {a} {a + k} (≤-steps′ {a} _)
  mod-helper0-+ᵃ-+ᵃ-+ᵃ a k (suc s) = mod-helper0-+ᵃ-+ᵃ-+ᵃ (suc a) k s

  -- seems like "mod-helper0-+ᵃ : ∀ {d n} → d ≤ n → mod-helper 0 n d n ≡ d"
  -- but with n ≡ k + d
  mod-helper0-+ᵃ-id-+ᵃ : ∀ k s → mod-helper 0 (k +ᵃ s) s (k +ᵃ s) ≡ s
  mod-helper0-+ᵃ-id-+ᵃ k s = mod-helper0-+ᵃ-+ᵃ-+ᵃ 0 k s

{-
  mod-helper0-+ᵃ-id-+ᵃ : ∀ k ack s → mod-helper 0 (k +ᵃ ack) (k +ᵃ s) (k +ᵃ ack) ≡ k +ᵃ s
  mod-helper0-+ᵃ-id-+ᵃ k ack zero rewrite +ᵃ0-identity k = {!mod-helper0-+ᵃ {k} {k + ack} (≤-steps′ {k} _)!}
  mod-helper0-+ᵃ-id-+ᵃ k ack (suc s) = {!mod-helper0-+ᵃ-id-+ᵃ (suc k) ack s!}

  mod-helper-s∸ : ∀ a a' {d s} → d ≤ s → mod-helper 0 (a +ᵃ s) (a' +ᵃ s ∸ d) (a +ᵃ s) ≡ a' +ᵃ s ∸ (mod-helper a (a' +ᵃ s) d s)
  mod-helper-s∸ a a' (z≤n {s}) = {!P.trans (mod-helper0-+ᵃ-id-+ᵃ a' a s)
                               {!(P.trans (P.sym (m+n∸n≡m s a))
                               (P.cong (λ z → z ∸ a) (P.trans (+-comm s a) (P.sym (+ᵃ-+ a s)))))!}!}
  mod-helper-s∸ a a' (s≤s p) = {!mod-helper-s∸ (suc a) (suc a') p!}
  -}

  mod-helper-s∸ : ∀ ack {d s} → d ≤ s → mod-helper 0 (ack +ᵃ s) (s ∸ d) (ack +ᵃ s) ≡ ack +ᵃ s ∸ (mod-helper ack (ack +ᵃ s) d s)
  mod-helper-s∸ ack (z≤n {s}) = P.trans (mod-helper0-+ᵃ-id-+ᵃ ack s)
                               (P.trans (P.sym (m+n∸n≡m s ack))
                               (P.cong (λ z → z ∸ ack) (P.trans (+-comm s ack) (P.sym (+ᵃ-+ ack s)))))
  mod-helper-s∸ ack (s≤s p) = mod-helper-s∸ (suc ack) p

  mod-helper0-s∸ : ∀ {d s} → d ≤ s → mod-helper 0 s (s ∸ d) s ≡ s ∸ (mod-helper 0 s d s)
  mod-helper0-s∸ = mod-helper-s∸ 0

-- Notice: d modℕ 0 ≡ d
-- One can argue that if one cannot divide by 0 then what remains is the whole thing.
-- Of course the remainder is not smaller than the divisor in this case.
_modℕ_ : (dividend divisor : ℕ) → ℕ
(d modℕ 0)     = d
(d modℕ suc s) = mod-helper 0 s d s

modℕ<divisor : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → dividend modℕ divisor < divisor
modℕ<divisor d 0 {}
modℕ<divisor d (suc s) = s≤s (mod-lemma 0 d s)

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
(d mod s) {≢0} = Fin.fromℕ≤ {d modℕ s} (modℕ<divisor d s {≢0})

ap-fromℕ≤ : ∀ {x y n}{p : x < n}{q : y < n} → x ≡ y → Fin.fromℕ≤ {x} {n} p ≡ Fin.fromℕ≤ {y} {n} q
ap-fromℕ≤ {x} {y} {n} {p} {q} e = FinP.toℕ-injective (begin
     toℕ (Fin.fromℕ≤ p)  ≡⟨ FinP.toℕ-fromℕ≤ p ⟩
     x                   ≡⟨ e ⟩
     y                   ≡⟨ P.sym (FinP.toℕ-fromℕ≤ q) ⟩
     toℕ (Fin.fromℕ≤ q)  ∎)

∸s-mod : ∀ {d s}{≢0 : False (s ≟ 0)} → s ≤ d → ((d ∸ s)mod s){≢0} ≡ (d mod s){≢0}
∸s-mod z≤n = P.refl
∸s-mod (s≤s s≤d) = ap-fromℕ≤ (mod-helper-+ᵃ-∸-+ᵃ 0 s≤d)

modℕ-<s : ∀ {d s}(p : d < s) → d modℕ s ≡ d
modℕ-<s (s≤s p) = mod-helper0-+ᵃ p

modℕ-∸s : ∀ {d s} → s ≤ d → (d ∸ s)modℕ s ≡ d modℕ s
modℕ-∸s z≤n = P.refl
modℕ-∸s (s≤s s≤d) = mod-helper-+ᵃ-∸-+ᵃ 0 s≤d

bar : ∀ x s → s ∸ x ≤ s
bar zero s = ℕ≤.refl
bar (suc x) zero = ℕ≤.refl
bar (suc x) (suc s) = ≤-step (bar x s)

gar : ∀ {x s} → 0 < x → 0 < s → s ∸ x < s
gar (s≤s (z≤n {x})) (s≤s (z≤n {s})) = s≤s (bar x s)

modℕ-s∸ : ∀ {x s} → 0 < x → x < s → (s ∸ x)modℕ s ≡ s ∸ (x modℕ s)
modℕ-s∸ {x} {s} 0<x x<s = begin
  (s ∸ x)modℕ s  ≡⟨ modℕ-<s (gar 0<x (ℕ≤.trans (s≤s z≤n) x<s)) ⟩
  s ∸ x          ≡⟨ P.cong (_∸_ s) (P.sym (modℕ-<s x<s)) ⟩
  s ∸ (x modℕ s) ∎

{-
mod-helper0-+ᵃ-suc-+ᵃ : ∀ k a s → mod-helper 0 (a +ᵃ k +ᵃ s) (a + suc s) (a +ᵃ k +ᵃ s) ≡ suc s
mod-helper0-+ᵃ-suc-+ᵃ k zero s = {!!}
mod-helper0-+ᵃ-suc-+ᵃ k (suc a) s = {!mod-helper0-+ᵃ-suc-+ᵃ (suc k) a s!}

Goal : ∀ a x s → x ≤ s → mod-helper 0 (a +ᵃ s) (suc s ∸ x) (a +ᵃ s) ≡ a +ᵃ suc s ∸ mod-helper a (a +ᵃ s) x s
Goal a .0 s z≤n = {!mod-helper0-+ᵃ-+ᵃ-+ᵃ 0!}
Goal a ._ ._ (s≤s p) = Goal (suc a) _ _ p

-- modℕ-s∸ : ∀ {x s} → x ≤ s → (s ∸ x)modℕ s ≡ s ∸ (x modℕ s)
modℕ-s∸ : ∀ {x s} → x < s → (s ∸ x)modℕ s ≡ s ∸ (x modℕ s)
modℕ-s∸ {s = zero} ()
modℕ-s∸ {x} {s = suc s} (s≤s p) = Goal 0 x s p
-}

{-
-- with ≤⇒∃ p
--... | k , e {-rewrite P.sym e-} =
  begin
  mod-helper 0 s (suc s ∸ x) s ≡⟨ {!mod-helper0-+ᵃ-id-+ᵃ (suc x) (suc s ∸ x)!} ⟩ -- mod-helper0-+ᵃ {suc s ∸ x} {s} {!≡+-≥ (suc s ∸ x) ? s!} ⟩
  suc s ∸ x ≡⟨ P.cong (λ z → suc s ∸ z) (P.sym (mod-helper0-+ᵃ {x} {s} p)) ⟩
  suc s ∸ mod-helper 0 s x s ∎
  {-
begin
  mod-helper 0 s (s ∸ x) s ≡⟨ {!!} ⟩
  mod-helper 0 s k s ≡⟨ mod-helper0-+ᵃ {k} {s} (≡+-≥ s x k (P.sym (P.cong pred e))) ⟩
  k ≡⟨ {!!} ⟩
  suc x + k ∸ x ≡⟨ P.cong (λ z → suc x + k ∸ z) (P.sym (mod-helper0-+ᵃ {x} {s} {!!})) ⟩
  suc s ∸ mod-helper 0 s x s ∎

{-
suc s ≡ k + x
mod-helper 0 s (k + x ∸ x) s ≡ suc s ∸ mod-helper 0 s x s
 
--{!P.trans ? ()!}
-}
-}
-}

-- Integer division with remainder.

private

  -- The quotient and remainder are related to the dividend and
  -- divisor in the right way.

  division-lemma :
    (mod-ack div-ack d n : ℕ) →
    let s = mod-ack + n in
    mod-ack + div-ack * suc s + d
      ≡
    mod-helper mod-ack s d n + div-helper div-ack s d n * suc s

  division-lemma mod-ack div-ack zero n = begin

    mod-ack + div-ack * suc s + zero  ≡⟨ +-right-identity _ ⟩

    mod-ack + div-ack * suc s         ∎

    where s = mod-ack + n

  division-lemma mod-ack div-ack (suc d) zero = begin

    mod-ack + div-ack * suc s + suc d                ≡⟨ solve 3
                                                              (λ mod-ack div-ack d →
                                                                   let s = mod-ack :+ con 0 in
                                                                   mod-ack :+ div-ack :* (con 1 :+ s) :+ (con 1 :+ d)
                                                                     :=
                                                                   (con 1 :+ div-ack) :* (con 1 :+ s) :+ d)
                                                              P.refl mod-ack div-ack d ⟩
    suc div-ack * suc s + d                          ≡⟨ division-lemma zero (suc div-ack) d s ⟩

    mod-helper zero          s      d  s    +
    div-helper (suc div-ack) s      d  s    * suc s  ≡⟨⟩

    mod-helper      mod-ack  s (suc d) zero +
    div-helper      div-ack  s (suc d) zero * suc s  ∎

    where s = mod-ack + 0

  division-lemma mod-ack div-ack (suc d) (suc n) = begin

    mod-ack + div-ack * suc s + suc d                   ≡⟨ solve 4
                                                                 (λ mod-ack div-ack n d →
                                                                      mod-ack :+ div-ack :* (con 1 :+ (mod-ack :+ (con 1 :+ n))) :+ (con 1 :+ d)
                                                                        :=
                                                                      con 1 :+ mod-ack :+ div-ack :* (con 2 :+ mod-ack :+ n) :+ d)
                                                                 P.refl mod-ack div-ack n d ⟩
    suc mod-ack + div-ack * suc s′ + d                  ≡⟨ division-lemma (suc mod-ack) div-ack d n ⟩

    mod-helper (suc mod-ack) s′ d n +
    div-helper      div-ack  s′ d n * suc s′            ≡⟨ P.cong (λ s → mod-helper (suc mod-ack) s d n +
                                                                         div-helper div-ack s d n * suc s)
                                                                  (P.sym (+-suc mod-ack n)) ⟩

    mod-helper (suc mod-ack) s d n +
    div-helper      div-ack  s d n * suc s              ≡⟨⟩

    mod-helper      mod-ack  s (suc d) (suc n) +
    div-helper      div-ack  s (suc d) (suc n) * suc s  ∎

    where
    s  = mod-ack + suc n
    s′ = suc mod-ack + n

divModPropℕ : ∀ d s → d ≡ d modℕ s + (d div s) * s
divModPropℕ _ zero    = P.sym (+-comm _ 0)
divModPropℕ d (suc s) = erase (division-lemma 0 0 d s)

divModProp : ∀ d s {≢0 : False (s ≟ 0)} → d ≡ toℕ ((d mod s){≢0}) + (d div s) * s
divModProp d (s) {≢0} = erase (begin
    d                                       ≡⟨ divModPropℕ d (s) ⟩
    d modℕ s + (d div s) * s                ≡⟨ P.cong₂ _+_ (P.sym (FinP.toℕ-fromℕ≤ lemma)) P.refl ⟩
    toℕ (Fin.fromℕ≤ lemma) + (d div s) * s  ∎)
  where lemma = modℕ<divisor d s {≢0}

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
(d divMod s) {≢0} = result (d div s) (d mod s) (divModProp d s {≢0})

div<≡0 : ∀ {d s} → d < s → d div s ≡ 0
div<≡0 {d} {zero}  d<s = P.refl
div<≡0 {d} {suc s} d<s = helper (≤-pred d<s)
  where
    helper : ∀ {d s n} → d ≤ n → div-helper 0 s d n ≡ 0
    helper z≤n       = P.refl
    helper (s≤s d≤n) = helper d≤n

d/d≡1 : ∀ d {≢0 : False (d ≟ 0)} → d div d ≡ 1
d/d≡1 zero {}
d/d≡1 (suc d) = helper d
  where
    helper : ∀ {s} d → div-helper 0 s (suc d) d ≡ 1
    helper zero    = P.refl
    helper (suc x) = helper x

1-modℕ : ∀ {s} → 1 < s → 1 modℕ s ≡ 1
1-modℕ = modℕ-<s

modℕ-prop : ∀ x {s} → x modℕ s ≡ x ∸ (x div s) * s
modℕ-prop x {s} = +-∸ x (x modℕ s) (x div s * s) (divModPropℕ x s)

{-
modℕ-ns∸ : ∀ {n x s} → 0 < x → x < n * s → (n * s ∸ x)modℕ s ≡ s ∸ (x modℕ s)
{-
modℕ-ns∸ {n} {x} {s} 0<x x<s =
    begin
    (n * s ∸ x)modℕ s      ≡⟨ {!!} ⟩
    s ∸ (x ∸ q1 * s)  ≡⟨ P.cong (_∸_ s) (P.sym (mod-prop x {s})) ⟩
    s ∸ (x modℕ s)         ∎
    where q1 = x div s
-}
modℕ-ns∸ {n} {x} {zero}  0<x x<s rewrite ℕ°.*-comm n 0 = P.refl
modℕ-ns∸ {n} {x} {suc s} 0<x x<s = helper n x s 0<x x<s
  where helper : ∀ n x s →
          0 < x →
          x < n * suc s →
          mod-helper 0 s (n * suc s ∸ x) s ≡ suc s ∸ mod-helper 0 s x s
        helper n zero    s p q = {!!}
        helper n (suc x) s p q = {!helper n x s!}

{-
suc s * n = n + s * n

(n + sn) ∸ x


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
