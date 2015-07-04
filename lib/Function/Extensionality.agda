{-# OPTIONS --without-K #-}
module Function.Extensionality where

-- See Function.Extensionality.Implicit for the extensionality of {x : A} → B x

open import Function
open import Relation.Binary.PropositionalEquality.Base

postulate
    FunExt : Set

module _ {a b}{A : Set a}{B : A → Set b} where
  infix 4 _∼_

  _∼_   : (f₀ f₁ : (x : A) → B x) → Set _
  f₀ ∼ f₁ = (x : A) → f₀ x ≡ f₁ x

  module _ {f₀ f₁ : (x : A) → B x} where
    happly : f₀ ≡ f₁ → f₀ ∼ f₁
    happly p x = ap (λ f₀ → f₀ x) p

    module _ {{fe : FunExt}} where
      postulate
        λ= : (f= : f₀ ∼ f₁) → f₀ ≡ f₁

        happly-λ= : (f= : f₀ ∼ f₁) → happly (λ= f=) ≡ f=

        λ=-happly : (α : f₀ ≡ f₁) → λ= (happly α) ≡ α

        -- This should be derivable if I had a proper proof of λ=
        ▸-λ= : ∀ {p x}(P : B x → Set p)(f= : f₀ ∼ f₁)
               → (λ f₀ → P (f₀ x)) ▸ λ= f= ≡ P ▸ f= x

      tr-λ= = ▸-λ=

      λ=ⁱ : (f= : ∀ {x} → f₀ x ≡ f₁ x) → f₀ ≡ f₁
      λ=ⁱ f= = λ= λ x → f= {x}

  !-α-λ= : ∀ {f₀ f₁ : (x : A) → B x}{{fe : FunExt}}
             (α : f₀ ≡ f₁) → ! α ≡ λ= (!_ ∘ happly α)
  !-α-λ= refl = ! λ=-happly refl

module _ {a b}{A : Set a}{B : A → Set b}{f₀ f₁ : (x : A) → B x}{{fe : FunExt}} where
  !-λ= : (f= : f₀ ∼ f₁) → ! (λ= f=) ≡ λ= (!_ ∘ f=)
  !-λ= f= = !-α-λ= (λ= f=) ∙ ap λ= (λ= (λ x → ap !_ (happly (happly-λ= f=) x)))
-- -}
-- -}
-- -}
