-- NOTE with-K
module Data.Nat.BoundedMonoInj-is-Id where

open import Type
open import Function.NP using (Endo)
open import Data.Zero using (𝟘 ; 𝟘-elim)
open import Data.Nat.NP
  using (ℕ; zero; suc; sucx≰x; module ℕ≤; _≤_; _<_; z≤n; s≤s; ≤-pred ; suc-injective; split-≤; <→≤)

open import Data.Nat.Properties using (≤-step; <-trans)
open import Data.Sum.NP using (inl ; inr)

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

Bounded-monotone : ℕ → Endo ℕ → ★
Bounded-monotone ub f = ∀ {x y} → x ≤ y → y < ub → f x ≤ f y

Bounded-injective : ℕ → Endo ℕ → ★
Bounded-injective ub f = ∀ {x y} → x < ub → y < ub → f x ≡ f y → x ≡ y

Bounded : ℕ → Endo ℕ → ★
Bounded ub f = ∀ x → x < ub → f x < ub

module From-mono-inj
           (f : ℕ → ℕ) {ub}
           (f-mono : Bounded-monotone ub f)
           (f-inj : Bounded-injective ub f)
         where

  f-mono-< : ∀ {x y} → x < y → y < ub → f x < f y
  f-mono-< p y<ub with split-≤ (f-mono (<→≤ p) y<ub)
  ... | inl q = 𝟘-elim (sucx≰x _ (subst (λ z → suc z ≤ _) (f-inj (<-trans p y<ub) y<ub q) p))
  ... | inr q = q

  is-id< : ∀ {b} → b < ub → Bounded (suc b) f → f b ≡ b
  is-id< {b} b<ub bub with split-≤ (bub b ℕ≤.refl)
  ... | inl p = suc-injective p
  ... | inr p = 𝟘-elim (bo b<ub (≤-pred p))
    where
      le : ∀ {n} → suc n < ub → f (suc n) ≤ n → f n < n
      le 1+n<ub p = ℕ≤.trans (f-mono-< ℕ≤.refl 1+n<ub) p
      bo : ∀ {b} → b < ub → ¬(f b < b)
      bo b<ub (s≤s p) = bo (ℕ≤.trans (s≤s (≤-step ℕ≤.refl)) b<ub) (le b<ub p)

  is-id≤ : ∀ b → b ≤ ub → Bounded b f → ∀ x → x < b → f x ≡ x
  is-id≤ zero b≤ub bub _ ()
  is-id≤ (suc b) b≤ub bub x pf with split-≤ pf
  ... | inl p rewrite suc-injective p = is-id< b≤ub bub
  ... | inr p = is-id≤ b (<→≤ b≤ub) ((λ y y<b → ℕ≤.trans (f-mono-< y<b b≤ub) (ℕ≤.reflexive (is-id< b≤ub bub)))) x (≤-pred p)

  is-id : Bounded ub f → ∀ x → x < ub → f x ≡ x
  is-id = is-id≤ ub ℕ≤.refl
