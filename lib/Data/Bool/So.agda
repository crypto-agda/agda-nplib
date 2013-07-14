open import Type
open import Data.Bool renaming (T to ✓)
open import Relation.Binary.PropositionalEquality

module Data.Bool.So where

data So : Bool → ★₀ where
  oh! : So true

So→✓ : ∀ {b} → So b → ✓ b
So→✓ oh! = _

✓→So : ∀ {b} → ✓ b → So b
✓→So {true}  _  = oh!
✓→So {false} ()

So→≡ : ∀ {b} → So b → b ≡ true
So→≡ oh! = refl

≡→So : ∀ {b} → b ≡ true → So b
≡→So refl = oh!
