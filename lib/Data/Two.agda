module Data.Two where

open import Type hiding (★)
open import Data.Product using (_×_; _,_)
import Data.Bool.NP as Bool
open Bool public hiding (if_then_else_) renaming (Bool to 𝟚; false to 0'; true to 1'; toℕ to 𝟚▹ℕ; toℕ≤1 to 𝟚≤1)

[0→_,1→_] : ∀ {a} {A : ★ a} → A → A → 𝟚 → A
[0→ e₀ ,1→ e₁ ] b = Bool.if b then e₁ else e₀

case_0→_1→_ : ∀ {a} {A : ★ a} → 𝟚 → A → A → A
case b 0→ e₀ 1→ e₁ = [0→ e₀ ,1→ e₁ ] b

proj : ∀ {a} {A : 𝟚 → ★ a} → A 0' × A 1' → (b : 𝟚) → A b
proj (x₀ , x₁) 0' = x₀
proj (x₀ , x₁) 1' = x₁

proj′ : ∀ {a} {A : ★ a} → A × A → 𝟚 → A
proj′ = proj

{-
explore𝟚 : ∀ {a} {A : ★ a} (_∙_ : A → A → A) (f : 𝟚 → A) → A
explore𝟚 _∙_ f = f 0' ∙ f 1'
-}
