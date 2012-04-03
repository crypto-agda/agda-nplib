module Data.Vec.NP where

open import Data.Vec public
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin
open import Data.Fin.Props
open import Data.Bool
open import Function

count : ∀ {n a} {A : Set a} → (A → Bool) → Vec A n → Fin (suc n)
count pred [] = zero
count pred (x ∷ xs) = (if pred x then suc else inject₁) (count pred xs)

filter : ∀ {n a} {A : Set a} (pred : A → Bool) (xs : Vec A n) → Vec A (toℕ (count pred xs))
filter pred [] = []
filter pred (x ∷ xs) with pred x
... | true  = x ∷ filter pred xs
... | false rewrite inject₁-lemma (count pred xs) = filter pred xs

η : ∀ {n a} {A : Set a} → Vec A n → Vec A n
η = tabulate ∘ flip lookup

η′ : ∀ {n a} {A : Set a} → Vec A n → Vec A n
η′ {zero}  = λ _ → []
η′ {suc n} = λ xs → head xs ∷ η (tail xs)
