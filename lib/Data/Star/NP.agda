{-# OPTIONS --without-K #-}
{-# OPTIONS --universe-polymorphism #-}
module Data.Star.NP where

open import Relation.Binary using (Rel;_⇒_)
open import Data.Star public
open import Function
-- import Category as Cat

Star⁻¹ : ∀ {ℓ a} {A : Set a} → Rel A ℓ → Rel A _
Star⁻¹ = flip ∘ Star ∘ flip

evalStar : ∀ {a p q} {A : Set a}
             {P : Rel A p} {Q : Rel A q} (idQ : ∀ {x} → Q x x)
             (_∘Q_ : ∀ {x y z} → Q y z → Q x y → Q x z)
           → (P ⇒ Q) → Star P ⇒ Q
evalStar {P = P} {Q} idQ _∘Q_ f = go where
  go : Star P ⇒ Q
  go ε = idQ
  go (x ◅ xs) = go xs ∘Q f x

{-
evalStar' : ∀ {A : Set}
              {P Q : Rel A} (catQ : Cat.RawCategory Q)
            → (P ⇒ Q) → Star P ⇒ Q
evalStar' {P = P} {Q} catQ f = go
  where open Cat.RawCategory catQ
        go : Star P ⇒ Q
        go ε        = id catQ
        go (x ◅ xs) = f x ∘ go xs
-}
