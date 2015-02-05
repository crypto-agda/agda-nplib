{-# OPTIONS --without-K #-}
module Data.Two.Base where

open import Data.Bool
  public
  hiding (if_then_else_)
  renaming (Bool to 𝟚; false to 0₂; true to 1₂; T to ✓)

open import Data.Product
  renaming (proj₁ to fst; proj₂ to snd)

open import Data.Sum
  using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)

open import Type using (★_)

open import Relation.Nullary using (¬_)

import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≢_; refl)

0≢1₂ : 0₂ ≢ 1₂
0≢1₂ ()

_² : ∀ {a} → ★ a → ★ a
A ² = 𝟚 → A

module _ {p} {P : 𝟚 → ★ p} where

    [0:_1:_] : P 0₂ → P 1₂ → (b : 𝟚) → P b
    [0: e₀ 1: e₁ ] 0₂ = e₀
    [0: e₀ 1: e₁ ] 1₂ = e₁

    tabulate₂ : ((b : 𝟚) → P b) → P 0₂ × P 1₂
    tabulate₂ f = f 0₂ , f 1₂

    η-[0:1:] : ∀ (f : (b : 𝟚) → P b) b → [0: f 0₂ 1: f 1₂ ] b ≡ f b
    η-[0:1:] f 0₂ = refl
    η-[0:1:] f 1₂ = refl

    proj : P 0₂ × P 1₂ → (b : 𝟚) → P b
    proj = uncurry [0:_1:_]

    proj-tabulate₂ : ∀ (f : (b : 𝟚) → P b) b → proj (tabulate₂ f) b ≡ f b
    proj-tabulate₂ = η-[0:1:]

module _ {a} {A : ★ a} where

    [0:_1:_]′ : A → A → A ²
    [0:_1:_]′ = [0:_1:_]

    case_0:_1:_ : 𝟚 → A → A → A
    case b 0: e₀ 1: e₁ = [0: e₀
                          1: e₁ ] b

    proj′ : A × A → A ²
    proj′ = proj

    proj[_] : 𝟚 → A × A → A
    proj[_] = [0: fst 1: snd ]

    mux : 𝟚 × (A × A) → A
    mux (s , eᵢ) = proj eᵢ s

nor : (b₀ b₁ : 𝟚) → 𝟚
nor b₀ b₁ = not (b₀ ∨ b₁)

nand : (b₀ b₁ : 𝟚) → 𝟚
nand b₀ b₁ = not (b₀ ∧ b₁)

-- For properties about _==_ see Data.Two.Equality
_==_ : (b₀ b₁ : 𝟚) → 𝟚
b₀ == b₁ = (not b₀) xor b₁

≡→✓ : ∀ {b} → b ≡ 1₂ → ✓ b
≡→✓ refl = _

≡→✓not : ∀ {b} → b ≡ 0₂ → ✓ (not b)
≡→✓not refl = _

✓→≡ : ∀ {b} → ✓ b → b ≡ 1₂
✓→≡ {1₂} _ = refl
✓→≡ {0₂} ()

✓not→≡ : ∀ {b} → ✓ (not b) → b ≡ 0₂
✓not→≡ {0₂} _ = refl
✓not→≡ {1₂} ()

-- See also ✓-∧
✓∧ : ∀ {b₁ b₂} → ✓ b₁ → ✓ b₂ → ✓ (b₁ ∧ b₂)
✓∧ {0₂} p q = p
✓∧ {1₂} p q = q

-- See also ✓-∧
✓∧₁ : ∀ {b₁ b₂} → ✓ (b₁ ∧ b₂) → ✓ b₁
✓∧₁ {0₂} ()
✓∧₁ {1₂} = _

✓∧₂ : ∀ {b₁ b₂} → ✓ (b₁ ∧ b₂) → ✓ b₂
✓∧₂ {0₂} ()
✓∧₂ {1₂} p = p

-- Similar to ✓-∨
✓∨-⊎ : ∀ {b₁ b₂} → ✓ (b₁ ∨ b₂) → ✓ b₁ ⊎ ✓ b₂
✓∨-⊎ {0₂} = inr
✓∨-⊎ {1₂} = inl

-- Similar to ✓-∨
✓∨₁ : ∀ {b₁ b₂} → ✓ b₁ → ✓ (b₁ ∨ b₂)
✓∨₁ {1₂} = _
✓∨₁ {0₂} ()

-- Similar to ✓-∨
✓∨₂ : ∀ {b₁ b₂} → ✓ b₂ → ✓ (b₁ ∨ b₂)
✓∨₂ {0₂} p = p
✓∨₂ {1₂} _ = _

✓-not-¬ : ∀ {b} → ✓ (not b) → ¬ (✓ b)
✓-not-¬ {0₂} _ = λ()
✓-not-¬ {1₂} ()

✓-¬-not : ∀ {b} → ¬ (✓ b) → ✓ (not b)
✓-¬-not {0₂} _ = _
✓-¬-not {1₂} f = f _

∧⇒∨ : ∀ x y → ✓ (x ∧ y) → ✓ (x ∨ y)
∧⇒∨ 0₂ _ = λ ()
∧⇒∨ 1₂ _ = _

-- This particular implementation has been
-- chosen for computational content.
-- Namely the proof is "re-created" when b is 1₂.
check : ∀ b → {pf : ✓ b} → ✓ b
check 0₂ {}
check 1₂ = _
