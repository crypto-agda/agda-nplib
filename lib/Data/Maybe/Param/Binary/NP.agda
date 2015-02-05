open import Type using (★_)
open import Function
open import Data.Maybe.Base
open import Data.Maybe.Param.Binary

module Data.Maybe.Param.Binary.NP where

  refl : ∀ {a p} {A : ★ a} {_∼_ : A → A → ★ p} (refl-A : ∀ x → x ∼ x) (mx : Maybe A) → ⟦Maybe⟧ _∼_ mx mx
  refl refl-A (just x) = ⟦just⟧ (refl-A x)
  refl refl-A nothing  = ⟦nothing⟧

  sym : ∀ {a b r₁ r₂} {A : ★ a} {B : ★ b} {_∼₁_ : A → B → ★ r₁} {_∼₂_ : B → A → ★ r₂}
          (sym-AB : ∀ {x y} → x ∼₁ y → y ∼₂ x) {mx : Maybe A} {my : Maybe B}
        → ⟦Maybe⟧ _∼₁_ mx my → ⟦Maybe⟧ _∼₂_ my mx
  sym sym-A (⟦just⟧ x∼₁y) = ⟦just⟧ (sym-A x∼₁y)
  sym sym-A ⟦nothing⟧     = ⟦nothing⟧

  trans : ∀ {a b c r₁ r₂ r₃} {A : ★ a} {B : ★ b} {C : ★ c}
            {_⟦AB⟧_ : A → B → ★ r₁}
            {_⟦BC⟧_ : B → C → ★ r₂}
            {_⟦AC⟧_ : A → C → ★ r₃}
            (trans : ∀ {x y z} → x ⟦AB⟧ y → y ⟦BC⟧ z → x ⟦AC⟧ z)
            {mx : Maybe A} {my : Maybe B} {mz : Maybe C}
          → ⟦Maybe⟧ _⟦AB⟧_ mx my → ⟦Maybe⟧ _⟦BC⟧_ my mz
          → ⟦Maybe⟧ _⟦AC⟧_ mx mz
  trans trans' (⟦just⟧ x∼y) (⟦just⟧ y∼z) = ⟦just⟧ (trans' x∼y y∼z)
  trans trans' ⟦nothing⟧    ⟦nothing⟧    = ⟦nothing⟧

  subst-⟦AB⟧ : ∀ {a b p q r} {A : ★ a} {B : ★ b}
                 (P : Maybe A → ★ p)
                 (Q : Maybe B → ★ q)
                 (⟦AB⟧ : A → B → ★ r)
                 (subst-⟦AB⟧-just : ∀ {x y} → ⟦AB⟧ x y → P (just x) → Q (just y))
                 (Pnothing→Qnothing : P nothing → Q nothing)
                 {mx : Maybe A} {my : Maybe B}
               → (⟦Maybe⟧ ⟦AB⟧ mx my) → P mx → Q my
  subst-⟦AB⟧ _ _ _ subst-⟦AB⟧-just _ (⟦just⟧ x∼y) Pmx = subst-⟦AB⟧-just x∼y Pmx
  subst-⟦AB⟧ _ _ _ _               f ⟦nothing⟧    Pnothing = f Pnothing

  subst : ∀ {a p r} {A : ★ a}
            (P : Maybe A → ★ p)
            (Aᵣ : A → A → ★ r)
            (subst-Aᵣ : ∀ {x y} → Aᵣ x y → P (just x) → P (just y))
            {mx my}
          → (⟦Maybe⟧ Aᵣ mx my) → P mx → P my
  subst P Aᵣ subst-Aᵣ = subst-⟦AB⟧ P P Aᵣ subst-Aᵣ id
