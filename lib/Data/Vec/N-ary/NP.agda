{-# OPTIONS --without-K #-}
module Data.Vec.N-ary.NP where

open import Type hiding (★)
open import Function
open import Data.Nat
open import Data.Vec.NP
open import Data.Vec.N-ary public renaming (curryⁿ to curryⁿ′; _$ⁿ_ to _$ⁿ′_)
open import Relation.Binary.PropositionalEquality.NP

module _ {a b} {A : ★ a} where
    curryⁿ : ∀ {n} {B : N-ary n A (★ b)} →
             ((xs : Vec A n) → B $ⁿ′ xs) → ∀ⁿ n B
    curryⁿ {zero}  f = f []
    curryⁿ {suc n} f = λ x → curryⁿ (f ∘ _∷_ x)

    _$ⁿ_ : ∀ {n} {B : N-ary n A (★ b)}
           → ∀ⁿ n B → ((xs : Vec _ n) → B $ⁿ′ xs)
    f $ⁿ []       = f
    f $ⁿ (x ∷ xs) = f x $ⁿ xs

    curry-$ⁿ : ∀ {n} {B : N-ary n A (★ b)}
                 (f : (xs : Vec A n) → B $ⁿ′ xs) (xs : Vec A n)
               → curryⁿ f $ⁿ xs ≡ f xs
    curry-$ⁿ f []       = idp
    curry-$ⁿ f (x ∷ xs) = curry-$ⁿ (f ∘ _∷_ x) xs

module _ {a b} {A : ★ a} {B : ★ b} where
    curry-$ⁿ′ : ∀ {n} (f : Vec A n → B) (xs : Vec A n)
                → curryⁿ′ f $ⁿ′ xs ≡ f xs
    curry-$ⁿ′ f []       = idp
    curry-$ⁿ′ f (x ∷ xs) = curry-$ⁿ′ (f ∘ _∷_ x) xs

    constⁿ : ∀ n → B → N-ary n A B
    constⁿ zero    x = x
    constⁿ (suc n) x = const (constⁿ n x)

    lift³ : (f g : N-ary 3 A B) → (∀ x y z → f x y z ≡ g x y z)
            → ∀ {n} (xs ys zs : Vec A n)
            → replicate f ⊛ xs ⊛ ys ⊛ zs ≡ replicate g ⊛ xs ⊛ ys ⊛ zs
    lift³ f g pf []       []       []       = idp
    lift³ f g pf (x ∷ xs) (y ∷ ys) (z ∷ zs) = ap-∷ (pf x y z) (lift³ f g pf xs ys zs)

module _ {m} where
  module _ {a b} {A : ★ a} {B : ★ b} where
    _≗ⁿ_ : (f g : N-ary m A B) → ★ _
    _≗ⁿ_ f g = ∀ⁿ m (curryⁿ′ (λ (xs : Vec A m) → f $ⁿ′ xs ≡ g $ⁿ′ xs))

  module _ {a b} {A : ★ a} {B : ★ b} where
    apⁿ : ∀ (f : N-ary m A B)
          → ∀ {n} → N-ary m (Vec A n) (Vec B n)
    apⁿ f = curryⁿ′ {m} (vap (_$ⁿ′_ f))

    liftⁿ : ∀ (f g : N-ary m A B)
            → f ≗ⁿ g
            → ∀ {n} → apⁿ f ≗ⁿ apⁿ g {n}
    liftⁿ f g pf = curryⁿ helper
      where f' = vap {m} (_$ⁿ′_ f)
            g' = vap {m} (_$ⁿ′_ g)
            h  = λ (xs : Vec _ m) → curryⁿ′ f' $ⁿ′ xs ≡ curryⁿ′ g' $ⁿ′ xs
            hh = λ (xs : Vec _ m) → f $ⁿ′ xs ≡ g $ⁿ′ xs
            helper : ∀ (xs : Vec _ m) → curryⁿ′ h $ⁿ′ xs
            helper xs = coe! (curry-$ⁿ′ h xs)
              (curry-$ⁿ′ f' xs ∙
               map-ext (λ ys → coe (curry-$ⁿ′ hh ys) (pf $ⁿ ys))
                       (transpose xs) ∙
              !(curry-$ⁿ′ g' xs))
