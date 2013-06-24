module Data.Nat.BoundedMonoInj-is-Id where

open import Type
open import Function.NP using (Endo)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat.NP using (ℕ; zero; suc; sucx≰x; module ℕ≤; _≤_; _<_; z≤n; s≤s; ≤-pred ; suc-injective)

open import Data.Nat.Properties using (≤-step; ≤-steps; <-trans)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

split-≤ : ∀ {x y} → x ≤ y → x ≡ y ⊎ x < y
split-≤ {zero} {zero} p = inj₁ refl
split-≤ {zero} {suc y} p = inj₂ (s≤s z≤n)
split-≤ {suc x} {zero} ()
split-≤ {suc x} {suc y} (s≤s p) with split-≤ {x} {y} p
... | inj₁ q rewrite q = inj₁ refl
... | inj₂ q = inj₂ (s≤s q)

<→≤ : ∀ {x y} → x < y → x ≤ y
<→≤ (s≤s p) = ≤-steps 1 p

Monotone : ℕ → Endo ℕ → ★
Monotone ub f = ∀ {x y} → x ≤ y → y < ub → f x ≤ f y

IsInj : ℕ → Endo ℕ → ★
IsInj ub f = ∀ {x y} → x < ub → y < ub → f x ≡ f y → x ≡ y

Bounded : ℕ → Endo ℕ → ★
Bounded ub f = ∀ x → x < ub → f x < ub

module M (f : ℕ → ℕ) {ub}
         (f-mono : Monotone ub f)
         (f-inj : IsInj ub f)
         (f-bounded : Bounded ub f) where

 f-mono-< : ∀ {x y} → x < y → y < ub → f x < f y
 f-mono-< {x} {y} p y<ub with split-≤ (f-mono {x} {y} (<→≤ p) y<ub)
 ... | inj₁ q = ⊥-elim (sucx≰x y (subst (λ z → suc z ≤ y) (f-inj {x} {y} (<-trans p y<ub) y<ub q) p))
 ... | inj₂ q = q

 le : ∀ n → suc n < ub → f (suc n) ≤ n → f n < n
 le n 1+n<ub p = ℕ≤.trans (f-mono-< {n} {suc n} ℕ≤.refl 1+n<ub) p

 fp : ∀ b → b < ub → Bounded (suc b) f → f b ≡ b
 fp b b<ub bub with split-≤ (bub b ℕ≤.refl)
 ... | inj₁ p = suc-injective p
 ... | inj₂ p = ⊥-elim (bo b b<ub (≤-pred p))
   where
     bo : ∀ b → b < ub → ¬(f b < b)
     bo zero _ ()
     bo (suc b) b<ub (s≤s p) = bo b (ℕ≤.trans (s≤s (≤-step ℕ≤.refl)) b<ub) (le b b<ub p)

 ob : ∀ b → b ≤ ub → Bounded b f → ∀ x → x < b → f x ≡ x
 ob zero b≤ub bub _ ()
 ob (suc b) b≤ub bub x pf with split-≤ pf
 ... | inj₁ p rewrite suc-injective p = fp b b≤ub bub
 ... | inj₂ (s≤s p) = ob b (<→≤ b≤ub) ((λ y y<b → ℕ≤.trans (f-mono-< y<b b≤ub) (ℕ≤.reflexive (fp b b≤ub bub)))) x p

 is-id : ∀ x → x < ub → f x ≡ x
 is-id = ob ub ℕ≤.refl f-bounded
