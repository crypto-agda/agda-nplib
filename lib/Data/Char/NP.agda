module Data.Char.NP where

open import Data.Char public
open import Data.List
open import Data.Bool
open import Function

notElem : Char → List Char → Bool
notElem c = null ∘ filter (_==_ c)

syntax notElem c cs = c `notElem` cs

elem : Char → List Char → Bool
elem c = not ∘ notElem c

syntax elem c cs = c `elem` cs
