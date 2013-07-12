{-# OPTIONS --without-K #-}
-- DEPRECATED module use Data.Two
module Data.Bool.NP where

-- No longer re-exporting Data.Bool
open import Data.Bool renaming (T to ✓)

open import Type hiding (★)
open import Function.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

cond : ∀ {a} {A : ★ a} → A → A → Bool → A
cond x y b = if b then x else y

Cond : ∀ {ℓ} (A : Bool → ★ ℓ) → A true → A false → Π Bool A
Cond _ x y true  = x
Cond _ x y false = y

If_then_else_ : ∀ {ℓ} {A B : ★ ℓ} b → (✓ b → A) → (✓ (not b) → B) → if b then A else B
If_then_else_ true  x _ = x _
If_then_else_ false _ x = x _

If′_then_else_ : ∀ {ℓ} {A B : ★ ℓ} b → A → B → if b then A else B
If′_then_else_ true  x _ = x
If′_then_else_ false _ x = x

If-map : ∀ {A B C D : ★₀} b (f : ✓ b → A → C) (g : ✓ (not b) → B → D) →
           if b then A else B → if b then C else D
If-map true  f _ = f _
If-map false _ f = f _

If-elim : ∀ {A B : ★₀} {P : Bool → ★₀}
            b (f : ✓ b → A → P true) (g : ✓ (not b) → B → P false) → if b then A else B → P b
If-elim true  f _ = f _
If-elim false _ f = f _

If-true : ∀ {A B : ★₀} {b} → ✓ b → (if b then A else B) ≡ A
If-true {b = true}  _ = ≡.refl
If-true {b = false} ()

If-false : ∀ {A B : ★₀} {b} → ✓ (not b) → (if b then A else B) ≡ B
If-false {b = true}  ()
If-false {b = false} _ = ≡.refl

cong-if : ∀ {A B : ★₀} b {t₀ t₁} (f : A → B) → (if b then f t₀ else f t₁) ≡ f (if b then t₀ else t₁)
cong-if true  _ = ≡.refl
cong-if false _ = ≡.refl

if-not : ∀ {a} {A : ★ a} b {t₀ t₁ : A} → (if b then t₀ else t₁) ≡ (if not b then t₁ else t₀)
if-not true  = ≡.refl
if-not false = ≡.refl
