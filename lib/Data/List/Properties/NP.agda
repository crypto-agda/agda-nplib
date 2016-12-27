{-# OPTIONS --without-K #-}
module Data.List.Properties.NP where

import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Type hiding (★)
open import Data.List.Properties public
open import Data.List.NP
open import Data.Nat.NP
open import Relation.Binary.PropositionalEquality.NP

module _ {a} {A : ★ a} where
    ∷= : ∀ {x y : A} {xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
    ∷= = ap₂ _∷_

    replicate-++ : ∀ {x : A} m n → replicate m x ++ replicate n x ≡ replicate (m + n) x
    replicate-++ zero     _  = refl
    replicate-++ (suc m)  n  = ap₂ _∷_ refl (replicate-++ m n)

    ++-assoc : ∀ xs {ys zs : List A} → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assoc []       = refl
    ++-assoc (x ∷ xs) = ap₂ _∷_ refl (++-assoc xs)

    take-++ : ∀ xs {ys : List A} → take (length xs) (xs ++ ys) ≡ xs
    take-++ []       = refl
    take-++ (x ∷ xs) = ap (_∷_ x) (take-++ xs)

    ap-head : ∀ {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
    ap-head refl = refl

    ap-tail : ∀ {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
    ap-tail refl = refl

    ++-inj : ∀ {xs ys zs ts : List A} → length xs ≡ length ys → xs ++ zs ≡ ys ++ ts → xs ≡ ys
    ++-inj {[]} {[]}         el ep = refl
    ++-inj {[]} {y ∷ ys}     () ep
    ++-inj {x ∷ xs} {[]}     () ep
    ++-inj {x ∷ xs} {y ∷ ys} el ep
      = ap₂ _∷_ (ap-head ep) (++-inj (ap pred el) (ap-tail ep))

    ++-length : ∀ {xs ys : List A} → length (xs ++ ys) ≡ length xs + length ys
    ++-length {[]}     = refl
    ++-length {x ∷ xs} = ap suc (++-length {xs})

    dup-length : (xs : List A) → length (dup xs) ≡ 2*(length xs)
    dup-length xs = ++-length {xs}

    dup-inj : Injective dup
    dup-inj {xs} {ys} e
      = ++-inj (2*-inj (! dup-length xs ∙ ap length e ∙ dup-length ys)) e
