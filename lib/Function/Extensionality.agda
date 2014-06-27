{-# OPTIONS --without-K #-}
module Function.Extensionality where

open import Function.NP
open import Relation.Binary.PropositionalEquality.NP  -- renaming (subst to tr)

happly : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x}
  → f ≡ g → (x : A) → f x ≡ g x
happly p x = ap (λ f → f x) p

postulate
    FunExt : Set
    λ= : ∀ {a b}{A : Set a}{B : A → Set b}{f₀ f₁ : (x : A) → B x}{{fe : FunExt}}
           (f= : ∀ x → f₀ x ≡ f₁ x) → f₀ ≡ f₁

    happly-λ= : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x}{{fe : FunExt}}
      (fg : ∀ x → f x ≡ g x) → happly (λ= fg) ≡ fg

    λ=-happly : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x}{{fe : FunExt}}
      (α : f ≡ g) → λ= (happly α) ≡ α

    -- This should be derivable if I had a proper proof of λ=
    tr-λ= : ∀ {a b p}{A : Set a}{B : A → Set b}{x}(P : B x → Set p)
              {f g : (x : A) → B x}{{fe : FunExt}}(fg : (x : A) → f x ≡ g x)
            → tr (λ f → P (f x)) (λ= fg) ≡ tr P (fg x)


!-α-λ= : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x}{{fe : FunExt}}
  (α : f ≡ g) → ! α ≡ λ= (!_ ∘ happly α)
!-α-λ= refl = ! λ=-happly refl

!-λ= : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x}{{fe : FunExt}}
  (fg : ∀ x → f x ≡ g x) → ! (λ= fg) ≡ λ= (!_ ∘ fg)
!-λ= fg = !-α-λ= (λ= fg) ∙ ap λ= (λ= (λ x → ap !_ (happly (happly-λ= fg) x)))
