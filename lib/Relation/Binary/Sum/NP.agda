{-# OPTIONS --without-K #-}
{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.Sum.NP where

open import Data.Sum
open import Relation.Binary
open import Relation.Binary.Sum public
open import Relation.Binary.Bijection
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_;_≢_)

private
 module Section {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂} where

  -- move this to Relation.Binary.Sum
  _⊎-preserve-bijections_ :
   ∀ {ℓ₁} {∼₁ : Rel A₁ ℓ₁}
     {ℓ₂} {∼₂ : Rel A₂ ℓ₂}
     (∼₁-bij : BijectiveREL A₁ A₁ ∼₁)
     (∼₂-bij : BijectiveREL A₂ A₂ ∼₂) →
     BijectiveREL (A₁ ⊎ A₂) (A₁ ⊎ A₂) (∼₁ ⊎-Rel ∼₂)
  _⊎-preserve-bijections_ {∼₁ = _∼₁_} {∼₂ = _∼₂_} ∼₁-bij ∼₂-bij
     = record { injectiveREL = λ {x} {y} {z} → inj {x} {y} {z}
              ; surjectiveREL = λ {x} {y} {z} → sur {x} {y} {z} }
     where
       ∼ = _∼₁_ ⊎-Rel _∼₂_
       A = A₁ ⊎ A₂
       open BijectiveREL ∼₁-bij renaming (injectiveREL to ∼₁-inj; surjectiveREL to ∼₁-sur)
       open BijectiveREL ∼₂-bij renaming (injectiveREL to ∼₂-inj; surjectiveREL to ∼₂-sur)
       inj : InjectiveREL A A ∼
       inj (₁∼₂ ()) _
       inj (₂∼₂ _) (₁∼₂ ())
       inj (₁∼₁ x∼₁z) (₁∼₁ y∼₁z) = ≡.cong inj₁ (∼₁-inj x∼₁z y∼₁z)
       inj (₂∼₂ x∼₂z) (₂∼₂ y∼₂z) = ≡.cong inj₂ (∼₂-inj x∼₂z y∼₂z)
       sur : SurjectiveREL A A ∼
       sur (₁∼₂ ()) _
       sur (₁∼₁ _) (₁∼₂ ())
       sur (₁∼₁ x∼₁y) (₁∼₁ x∼₁y') = ≡.cong inj₁ (∼₁-sur x∼₁y x∼₁y')
       sur (₂∼₂ x∼₂y) (₂∼₂ x∼₂y') = ≡.cong inj₂ (∼₂-sur x∼₂y x∼₂y')

open Section public
