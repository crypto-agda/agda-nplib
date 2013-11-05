{-# OPTIONS --without-K #-}
module Data.Two where

open import Data.Bool public hiding (if_then_else_) renaming (Bool to 𝟚; false to 0₂; true to 1₂; T to ✓)
open import Data.Bool.Properties
  public
  using (isCommutativeSemiring-∨-∧
        ;commutativeSemiring-∨-∧
        ;module RingSolver
        ;isCommutativeSemiring-∧-∨
        ;commutativeSemiring-∧-∨
        ;isBooleanAlgebra
        ;booleanAlgebra
        ;commutativeRing-xor-∧
        ;module XorRingSolver
        ;not-involutive
        ;not-¬
        ;¬-not
        ;⇔→≡
        ;proof-irrelevance)
  renaming
        (T-≡ to ✓-≡
        ;T-∧ to ✓-∧
        ;T-∨ to ✓-∨)

open import Type using (★_)

open import Algebra                    using (module CommutativeRing; module CommutativeSemiring)
open import Algebra.FunctionProperties using (Op₁; Op₂)

open import Data.Nat     using (ℕ; _≤_; z≤n; s≤s; _⊓_; _⊔_; _∸_)
open import Data.Zero    using (𝟘-elim)
open import Data.One     using (𝟙)
open import Data.Product using (proj₁; proj₂; uncurry; _×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)

open import Function.Equivalence using (module Equivalence)
open import Function.Equality    using (_⟨$⟩_)
open import Function.NP          using (id; _∘_; _⟨_⟩°_)

open import Relation.Binary.PropositionalEquality.NP using (_≡_; _≢_; refl; idp; _∙_; !)
open import Relation.Nullary                         using (¬_; Dec; yes; no)

open Equivalence using (to; from)

module Xor° = CommutativeRing     commutativeRing-xor-∧
module 𝟚°   = CommutativeSemiring commutativeSemiring-∧-∨

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

    [0:_1:_]′ : A → A → 𝟚 → A
    [0:_1:_]′ = [0:_1:_]

    case_0:_1:_ : 𝟚 → A → A → A
    case b 0: e₀ 1: e₁ = [0: e₀
                          1: e₁ ] b

    proj′ : A × A → 𝟚 → A
    proj′ = proj

    proj[_] : 𝟚 → A × A → A
    proj[_] = [0: proj₁ 1: proj₂ ]

    mux : 𝟚 × (A × A) → A
    mux (s , eᵢ) = proj eᵢ s

nor : (b₀ b₁ : 𝟚) → 𝟚
nor b₀ b₁ = not (b₀ ∨ b₁)

nand : (b₀ b₁ : 𝟚) → 𝟚
nand b₀ b₁ = not (b₀ ∧ b₁)

_==_ : (b₀ b₁ : 𝟚) → 𝟚
b₀ == b₁ = (not b₀) xor b₁

==-refl : ∀ {b} → ✓ (b == b)
==-refl {1₂} = _
==-refl {0₂} = _

==-reflexive : ∀ {x y} → x ≡ y → ✓(x == y)
==-reflexive {x} refl = ==-refl {x}

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

✓∧ : ∀ {b₁ b₂} → ✓ b₁ → ✓ b₂ → ✓ (b₁ ∧ b₂)
✓∧ p q = _⟨$⟩_ (from ✓-∧) (p , q)

✓∧₁ : ∀ {b₁ b₂} → ✓ (b₁ ∧ b₂) → ✓ b₁
✓∧₁ = proj₁ ∘ _⟨$⟩_ (to ✓-∧)

✓∧₂ : ∀ {b₁ b₂} → ✓ (b₁ ∧ b₂) → ✓ b₂
✓∧₂ {b₁} = proj₂ ∘ _⟨$⟩_ (to (✓-∧ {b₁}))

✓∨-⊎ : ∀ {b₁ b₂} → ✓ (b₁ ∨ b₂) → ✓ b₁ ⊎ ✓ b₂
✓∨-⊎ {b₁} = _⟨$⟩_ (to (✓-∨ {b₁}))

✓∨₁ : ∀ {b₁ b₂} → ✓ b₁ → ✓ (b₁ ∨ b₂)
✓∨₁ = _⟨$⟩_ (from ✓-∨) ∘ inj₁

✓∨₂ : ∀ {b₁ b₂} → ✓ b₂ → ✓ (b₁ ∨ b₂)
✓∨₂ {b₁} = _⟨$⟩_ (from (✓-∨ {b₁})) ∘ inj₂

✓-not-¬ : ∀ {b} → ✓ (not b) → ¬ (✓ b)
✓-not-¬ {0₂} _ = λ()
✓-not-¬ {1₂} ()

✓-¬-not : ∀ {b} → ¬ (✓ b) → ✓ (not b)
✓-¬-not {0₂} _ = _
✓-¬-not {1₂} f = f _

∧⇒∨ : ∀ x y → ✓ (x ∧ y) → ✓ (x ∨ y)
∧⇒∨ 0₂ _ = λ ()
∧⇒∨ 1₂ _ = _

✓dec : ∀ b → Dec (✓ b)
✓dec = [0: no (λ())
        1: yes _ ]

de-morgan : ∀ x y → not (x ∨ y) ≡ not x ∧ not y
de-morgan 0₂ _ = refl
de-morgan 1₂ _ = refl

≢0→≡1 : ∀ {x} → x ≢ 0₂ → x ≡ 1₂
≢0→≡1 {1₂} p = refl
≢0→≡1 {0₂} p = 𝟘-elim (p refl)

≢1→≡0 : ∀ {x} → x ≢ 1₂ → x ≡ 0₂
≢1→≡0 {0₂} p = refl
≢1→≡0 {1₂} p = 𝟘-elim (p refl)

-- 0₂ is 0 and 1₂ is 1
𝟚▹ℕ : 𝟚 → ℕ
𝟚▹ℕ = [0: 0
       1: 1 ]

𝟚▹ℕ≤1 : ∀ b → 𝟚▹ℕ b ≤ 1
𝟚▹ℕ≤1 = [0: z≤n
         1: s≤s z≤n ]

𝟚▹ℕ-⊓ : ∀ a b → 𝟚▹ℕ a ⊓ 𝟚▹ℕ b ≡ 𝟚▹ℕ (a ∧ b)
𝟚▹ℕ-⊓ 1₂ 0₂ = refl
𝟚▹ℕ-⊓ 1₂ 1₂ = refl
𝟚▹ℕ-⊓ 0₂ _  = refl

𝟚▹ℕ-⊔ : ∀ a b → 𝟚▹ℕ a ⊔ 𝟚▹ℕ b ≡ 𝟚▹ℕ (a ∨ b)
𝟚▹ℕ-⊔ 1₂ 0₂ = refl
𝟚▹ℕ-⊔ 1₂ 1₂ = refl
𝟚▹ℕ-⊔ 0₂ _  = refl

𝟚▹ℕ-∸ : ∀ a b → 𝟚▹ℕ a ∸ 𝟚▹ℕ b ≡ 𝟚▹ℕ (a ∧ not b)
𝟚▹ℕ-∸ 0₂ 0₂ = refl
𝟚▹ℕ-∸ 0₂ 1₂ = refl
𝟚▹ℕ-∸ 1₂ 0₂ = refl
𝟚▹ℕ-∸ 1₂ 1₂ = refl

xor-not-not : ∀ x y → (not x) xor (not y) ≡ x xor y
xor-not-not 0₂ y = not-involutive y
xor-not-not 1₂ _ = refl

not-inj : ∀ {x y} → not x ≡ not y → x ≡ y
not-inj {0₂} {0₂} _ = refl
not-inj {1₂} {1₂} _ = refl
not-inj {0₂} {1₂} ()
not-inj {1₂} {0₂} ()

xor-inj₁ : ∀ x {y z} → (x xor y) ≡ (x xor z) → y ≡ z
xor-inj₁ 0₂ = id
xor-inj₁ 1₂ = not-inj

xor-inj₂ : ∀ x {y z} → (y xor x) ≡ (z xor x) → y ≡ z
xor-inj₂ x {y} {z} p = xor-inj₁ x (Xor°.+-comm x y ∙ p ∙ Xor°.+-comm z x)

check : ∀ b → {pf : ✓ b} → 𝟙
check = _

module Indexed {a} {A : ★ a} where
    _∧°_ : Op₂ (A → 𝟚)
    x ∧° y = x ⟨ _∧_ ⟩° y

    _∨°_ : Op₂ (A → 𝟚)
    x ∨° y = x ⟨ _∨_ ⟩° y

    _xor°_ : Op₂ (A → 𝟚)
    x xor° y = x ⟨ _xor_ ⟩° y

    _==°_ : Op₂ (A → 𝟚)
    x ==° y = x ⟨ _==_ ⟩° y

    not° : Op₁ (A → 𝟚)
    not° f = not ∘ f
-- -}
-- -}
-- -}
