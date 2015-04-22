{-# OPTIONS --without-K #-}
module Data.Nat.Primality.NP where

open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Nat.Divisibility.NP
open import Data.Nat.Primality public
  hiding (prime?) -- was slow

open import Data.Fin.Dec
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation
open import Relation.Nullary

-- same code but imports the fast _∣?_
prime? : Decidable Prime
prime? 0             = no λ()
prime? 1             = no λ()
prime? (suc (suc n)) = all? λ _ → ¬? (_ ∣? _)

prime-≥2 : ∀ {n} → Prime n → n ≥ 2
prime-≥2 {0}    ()
prime-≥2 {1}    ()
prime-≥2 {2+ _} _ = s≤s (s≤s z≤n)

prime-≢0 : ∀ {n} → Prime n → n ≢ 0
prime-≢0 {0}    () _
prime-≢0 {1+ _} _  ()

prime-≢1 : ∀ {n} → Prime n → n ≢ 1
prime-≢1 {0}    () _
prime-≢1 {1}    () _
prime-≢1 {2+ _} _  ()
