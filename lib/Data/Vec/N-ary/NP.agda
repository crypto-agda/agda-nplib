module Data.Vec.N-ary.NP where

open import Function
open import Data.Nat
open import Data.Vec
open import Data.Vec.N-ary public renaming (curryⁿ to curryⁿ′; _$ⁿ_ to _$ⁿ′_)
open import Relation.Binary.PropositionalEquality

curryⁿ : ∀ {n a b} {A : Set a} {B : N-ary n A (Set b)} →
         ((xs : Vec A n) → B $ⁿ′ xs) → ∀ⁿ n B
curryⁿ {zero}  f = f []
curryⁿ {suc n} f = λ x → curryⁿ (f ∘ _∷_ x)

_$ⁿ_ : ∀ {n a b} {A : Set a} {B : N-ary n A (Set b)} → ∀ⁿ n B → ((xs : Vec A n) → B $ⁿ′ xs)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

curry-$ⁿ : ∀ {n a b} {A : Set a} {B : N-ary n A (Set b)} (f : (xs : Vec A n) → B $ⁿ′ xs) (xs : Vec A n)
           → curryⁿ f $ⁿ xs ≡ f xs
curry-$ⁿ f []       = refl
curry-$ⁿ f (x ∷ xs) = curry-$ⁿ (f ∘ _∷_ x) xs

curry-$ⁿ′ : ∀ {n a b} {A : Set a} {B : Set b} (f : Vec A n → B) (xs : Vec A n)
           → curryⁿ′ f $ⁿ′ xs ≡ f xs
curry-$ⁿ′ f []       = refl
curry-$ⁿ′ f (x ∷ xs) = curry-$ⁿ′ (f ∘ _∷_ x) xs
