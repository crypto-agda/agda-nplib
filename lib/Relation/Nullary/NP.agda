module Relation.Nullary.NP where

open import Type
open import Function
open import Data.Zero
open import Data.One
open import Data.Sum
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary public

Dec-𝟘 : Dec 𝟘
Dec-𝟘 = no id

Dec-𝟙 : Dec 𝟙
Dec-𝟙 = yes _

module _ {a b} {A : ★_ a} {B : ★_ b} where
    Dec-⊎ : Dec A → Dec B → Dec (A ⊎ B)
    Dec-⊎ (yes p) _       = yes (inj₁ p)
    Dec-⊎ (no ¬p) (yes q) = yes (inj₂ q)
    Dec-⊎ (no ¬p) (no ¬q) = no [ ¬p , ¬q ]

    Dec-× : Dec A → Dec B → Dec (A × B)
    Dec-× (no ¬p) _       = no  (¬p ∘ fst)
    Dec-× (yes _) (no ¬q) = no  (¬q ∘ snd)
    Dec-× (yes p) (yes q) = yes (p , q)

    Dec-→ : Dec A → Dec B → Dec (A → B)
    Dec-→ _       (yes q) = yes (λ _ → q)
    Dec-→ (no ¬p) _       = yes (𝟘-elim ∘ ¬p)
    Dec-→ (yes p) (no ¬q) = no  (λ f → ¬q (f p))

    module _ (to : A → B)(from : B → A) where

      map-Dec : Dec A → Dec B
      map-Dec (yes p) = yes (to p)
      map-Dec (no ¬p) = no  (¬p ∘ from)
