{-# OPTIONS --without-K #-}
module Function.Extensionality where

open import Relation.Binary.PropositionalEquality renaming (subst to tr)

postulate
    FunExt : Set
    λ= : ∀ {a b}{A : Set a}{B : A → Set b}{f₀ f₁ : (x : A) → B x}(f= : ∀ x → f₀ x ≡ f₁ x){{fe : FunExt}} → f₀ ≡ f₁

    -- This should be derivable if I had a proper proof of λ=
    tr-λ= : ∀ {a b p}{A : Set a}{B : A → Set b}{x}(P : B x → Set p)
              {f g : (x : A) → B x}(fg : (x : A) → f x ≡ g x){{fe : FunExt}}
            → tr (λ f → P (f x)) (λ= fg) ≡ tr P (fg x)
