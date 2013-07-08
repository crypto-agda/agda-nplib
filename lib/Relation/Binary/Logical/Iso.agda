module Relation.Binary.Logical.Iso where

open import Type using (★_)
open import Level.NP using (₀; ₁)
open import Data.Product.NP using (_,_)
open import Relation.Binary using (Setoid; module Setoid)
open import Function.Inverse.NP using (_$₁_;_$₂_;id;_∈_) renaming (Inverse to _≅_; module Inverse to ≅; inverses to isomorphism)
open import Function.Equality as FE using (_⟶_; _⇨_; _⟨$⟩_; cong)

module _ {a₁ a₂ aᵣ} {A₁ : Setoid a₁ aᵣ} {A₂ : Setoid a₂ aᵣ} (Aᵣ : A₁ ≅ A₂)
         {b₁ b₂ bᵣ} {B₁ : Setoid b₁ bᵣ} {B₂ : Setoid b₂ bᵣ} (Bᵣ : B₁ ≅ B₂)
         where

    private
        module A₁ˢ = Setoid A₁
        module A₂ˢ = Setoid A₂
        module B₁ˢ = Setoid B₁
        module B₂ˢ = Setoid B₂
        S = A₁ ⟶ B₁
        T = A₂ ⟶ B₂
        to : S → T
        to f = ≅.to Bᵣ FE.∘ f FE.∘ ≅.from Aᵣ
        from : T → S
        from f = ≅.from Bᵣ FE.∘ f FE.∘ ≅.to Aᵣ
        to∘from : ∀ (f : T) x → to (from f) ⟨$⟩ x B₂ˢ.≈ f ⟨$⟩ x
        to∘from f x = B₂ˢ.trans (≅.right-inverse-of Bᵣ (f ⟨$⟩ (Aᵣ $₁ (Aᵣ $₂ x)))) (cong f (≅.right-inverse-of Aᵣ x))
        from∘to : ∀ (f : S) x → from (to f) ⟨$⟩ x B₁ˢ.≈ f ⟨$⟩ x
        from∘to f x = B₁ˢ.trans (≅.left-inverse-of Bᵣ (f ⟨$⟩ (Aᵣ $₂ (Aᵣ $₁ x)))) (cong f (≅.left-inverse-of Aᵣ x))

{-
    infixr 1 _⟪→⟫_

    _⟪→⟫_ : (A₁ ⇨ B₁) ≅ (A₂ ⇨ B₂)
    _⟪→⟫_ = record { to = record { _⟨$⟩_ = to
                                 ; cong = {!!} }
                   ; from = record { _⟨$⟩_ = from
                                   ; cong = {!!} }
                   ; inverse-of = record { left-inverse-of = λ f s → {!from∘to f ? !}
                                         ; right-inverse-of = {!!} } }
-}

open import Relation.Binary.PropositionalEquality as ≡

open import Data.Two using (𝟚; 0₂; 1₂; not)
open import Data.Bool.Properties

𝟚ˢ : Setoid ₀ ₀
𝟚ˢ = ≡.setoid 𝟚
⟪𝟚⟫ : 𝟚ˢ ≅ 𝟚ˢ
⟪𝟚⟫ = id
⟪0₂⟫ : (0₂ , 0₂) ∈ ⟪𝟚⟫
⟪0₂⟫ = refl
⟪1₂⟫ : (1₂ , 1₂) ∈ ⟪𝟚⟫
⟪1₂⟫ = refl
--⟪not⟫₂ : (Δ (→-to-⟶ not)) ∈ (⟪𝟚⟫ ⟪→⟫ ⟪𝟚⟫)
--⟪not⟫₂ refl = refl

-- 'not' is an isomorphism on '𝟚' and so can be used as an “equality” on '𝟚'
⟪not⟫ : 𝟚ˢ ≅ 𝟚ˢ
⟪not⟫ = isomorphism not not not-involutive not-involutive

⟪0₂1₂⟫ : (0₂ , 1₂) ∈ ⟪not⟫
⟪0₂1₂⟫ = refl
⟪1₂0₂⟫ : (0₂ , 1₂) ∈ ⟪not⟫
⟪1₂0₂⟫ = refl

--⟪not⟫'' : (Δ (→-to-⟶ not)) ∈ (⟪not⟫ ⟪→⟫ ⟪not⟫)
--⟪not⟫'' refl = not-involutive _

-- since 𝟚ʳ is not reflexive it cannot be an equivalence relation and
-- thus cannot be used to build a setoid.
data 𝟚ʳ : 𝟚 → 𝟚 → ★ ₀ where
  0₂1₂ : 𝟚ʳ 0₂ 1₂
  1₂0₂ : 𝟚ʳ 1₂ 0₂

open import Data.Nat.NP using (ℕ; zero; suc; ℕˢ)
⟪ℕ⟫ : ℕˢ ≅ ℕˢ
⟪ℕ⟫ = id
⟪zero⟫ : (zero , zero) ∈ ⟪ℕ⟫
⟪zero⟫ = refl
--⟪suc⟫ : (→-to-⟶ suc , →-to-⟶ suc) ∈ (⟪ℕ⟫ ⟪→⟫ ⟪ℕ⟫)
--⟪suc⟫ refl = refl
