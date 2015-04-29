{-# OPTIONS --without-K #-}
module Type.Eq where

open import Data.Two
              renaming (_==_ to _==𝟚_)
open import Relation.Binary.PropositionalEquality
              renaming (cong to ap; cong₂ to ap₂)
open import Data.Product
              renaming (proj₁ to fst; proj₂ to snd)

record Eq? {a} (A : Set a) : Set a where
  field
    _==_ : A → A → 𝟚
    ≡⇒== : ∀ {x y} → x ≡ y → ✓ (x == y)
    ==⇒≡ : ∀ {x y} → ✓ (x == y) → x ≡ y

open Eq? {{...}} public

𝟚-Eq? : Eq? 𝟚
𝟚-Eq? = record { _==_ = _==𝟚_
               ; ≡⇒== = λ { {0₂} .{0₂} refl → _
                          ; {1₂} .{1₂} refl → _
                          }
               ; ==⇒≡ = λ { {0₂} {0₂} _ → refl
                          ; {1₂} {1₂} _ → refl
                          ; {0₂} {1₂} ()
                          ; {1₂} {0₂} ()
                          }
               }

module _ {a b}{A : Set a}{B : Set b}
         {{A-eq? : Eq? A}}
         {{B-eq? : Eq? B}} where
  instance
    ×-Eq? : Eq? (A × B)
    ×-Eq? = record
      { _==_ = λ x y → fst x == fst y ∧ snd x == snd y
      ; ≡⇒== = λ e → ✓∧ (≡⇒== (ap fst e)) (≡⇒== (ap snd e))
      ; ==⇒≡ = λ e → let p = ✓∧× e in
                      ap₂ _,_ (==⇒≡ (fst p))
                              (==⇒≡ (snd p))
      }
