module Relation.Nullary.NP where

open import Type
open import Function
open import Data.Zero
open import Data.One
open import Data.Sum
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary public

[yes:_no:_] : ∀ {a b}{A : ★_ a}
                {B : Dec A → ★_ b}
                (B-yes : (x : A)   → B (yes x))
                (B-no  : (x : ¬ A) → B (no  x))
                (d : Dec A)
              → B d
[yes: B-yes no: B-no ] (yes p) = B-yes p
[yes: B-yes no: B-no ] (no ¬p) = B-no ¬p

elim-Dec : ∀ {a b}{A : ★_ a}
             (B : Dec A → ★_ b)
             (B-yes : (x : A)   → B (yes x))
             (B-no  : (x : ¬ A) → B (no  x))
             (d : Dec A)
           → B d
elim-Dec B = [yes:_no:_]

[yes:_no:_]′ : ∀ {a b}{A : ★_ a}
                 {B : ★_ b}
                 (B-yes : (x : A)   → B)
                 (B-no  : (x : ¬ A) → B)
                 (d : Dec A)
               → B
[yes:_no:_]′ = [yes:_no:_]

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

    -- also available as Relation.Nullary.Decidable.map′
    module _ (to : A → B)(from : B → A) where

      map-Dec : Dec A → Dec B
      map-Dec (yes p) = yes (to p)
      map-Dec (no ¬p) = no  (¬p ∘ from)
