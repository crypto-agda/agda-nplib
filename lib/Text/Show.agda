module Text.Show where

open import Level.NP         using (₀)
open import Function         using (id; _∘_; case_of_)
open import Data.Bool.Base   using (Bool; false; true)
open import Data.Nat.Base    using (ℕ)
open import Data.List.Base   using (List; []; _∷_; _++_; [_])
open import Data.String.Base using (String; fromList) renaming (_++_ to _++ₛ_)
open import Data.Char.Base   using (Char)

ShowS = List String → List String

private
  concat : List String → String
  concat []       = ""
  concat (x ∷ xs) = x ++ₛ concat xs

record Show {a} (A : Set a) : Set a where
  constructor mk

  field
    showsPrec : (prec : ℕ) → A → ShowS

  shows : A → ShowS
  shows = showsPrec 0

  show : A → String
  show x = concat (shows x [])

open Show {{...}} public

showString : String → ShowS
showString = _++_ ∘ [_]

showChar : Char → ShowS
showChar = showString ∘ fromList ∘ [_]

showParen : Bool → ShowS → ShowS
showParen true  s = showString "(" ∘ s ∘ showString ")"
showParen false s = s 

showListWith : ∀ {a}{A : Set a}(showA : A → ShowS) → List A → ShowS
showListWith showA [] = showString "[]"
showListWith showA (x ∷ xs) = showString "[" ∘ showA x ∘ go xs ∘ showString "]"
  where go : List _ → _
        go []       = id
        go (y ∷ ys) = showString ", " ∘ showA y ∘ go ys

showConsList : ∀ {a}{A : Set a}{{showA : Show A}} → Show (List A)
showConsList = mk λ _ → go
    where go : List _ → ShowS
          go []       = showString "[]"
          go (x ∷ xs) = shows x ∘ showString " ∷ " ∘ go xs

instance
  ShowBool : Show Bool
  ShowBool = mk λ _ b → showString (case b of λ { true → "true" ; false → "false" })

  ShowList : ∀ {a}{A : Set a}{{showA : Show A}} → Show (List A)
  ShowList = mk λ _ → showListWith shows

  ShowString : Show String
  ShowString = mk λ _ → showString ∘ Data.String.Base.show

  ShowChar : Show Char
  ShowChar = mk λ _ → showString ∘ Data.Char.Base.show
