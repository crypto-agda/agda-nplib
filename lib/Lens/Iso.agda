{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Lens.Type
open import Category.Functor
open import Category.Profunctor
open import Data.Bool
open import Data.Product
open import Data.Maybe
open import Data.Default

module Lens.Iso where

Iso : (S T A B : ★) → ★₁
Iso S T A B = ∀ {_↝_ F} {{↝Pro : Profunctor _↝_}} {{Ffun : RawFunctor F}}
              → A ↝ F B → S ↝ F T
           -- alternatively
           -- → Overloading′ _↝_ F S T A B

Iso′ : (S A : ★) → ★₁
Iso′ S A = Iso S S A A

iso : ∀ {S T A B} → (S → A) → (B → T) → Iso S T A B
iso f f⁻¹ = lmap f ∘ rmap (_<$>_ f⁻¹)
  where open Profunctor {{...}}
        open RawFunctor {{...}}

AnIso : (S T A B : ★) → ★
AnIso S T A B = Exchange A A B → Exchange A S T
-- alternatively
-- AnIso S T A B = Overloading (Exchange A) (Exchange A) id S T A B

AnIso′ : (S A : ★) → ★
AnIso′ = Simple AnIso

withIso : ∀ {S T A B R : ★} {{_ : Default B}} → ((S → A) → (B → T) → R) → AnIso S T A B → R
withIso {B = B} k ai = k sa bt
  where open Exchanges
        postulate
          -- this postulate is safe since an input B is asked for
          -- and so B cannot be the empty type
          bad-use-of-withIso : {{_ : Default B}} → B
        go = ai ∘ _,_ id
        sa = exchange (go bad-use-of-withIso)
        bt = extract ∘ go

from : ∀ {S T A B} {{_ : Default B}} → AnIso S T A B → Iso B A T S
from η = withIso (λ f g → iso g f) η

cloneIso : ∀ {S T A B} {{_ : Default B}} → AnIso S T A B → Iso S T A B
cloneIso η = withIso (λ f g → iso f g) η

au : ∀ {S T A B E} {{_ : Default B}} → AnIso S T A B → ((S → A) → E → B) → E → T
au η = withIso (λ sa bt f e → bt (f sa e)) η

auf : ∀ {S T A B R E} {{_ : Default B}} → AnIso S T A B → ((R → A) → E → B) → (R → S) → E → T
auf η = withIso (λ sa bt f g e → bt (f (sa ∘ g) e)) η

under : ∀ {S T A B} {{_ : Default B}} → AnIso S T A B → (T → S) → (B → A)
under η = withIso (λ f g h → f ∘ h ∘ g) η

mapping : ∀ {F S T A B} {{_ : Default B}} {{Ffun : RawFunctor F}}
          → AnIso S T A B → Iso (F S) (F T) (F A) (F B)
mapping η = withIso (λ f g → iso (_<$>_ f) (_<$>_ g)) η
  where open RawFunctor {{...}}

simple : ∀ {A} → Iso′ A A
simple = id

private
  module AnIso∘-is-∘ {S T A B C}
                     (i : AnIso S T A B) (i' : AnIso A B A C) where
    i∘i' : AnIso S T A C
    i∘i' = i ∘ i'

    i∘i'′ : AnIso _ _ _ _
    i∘i'′ = i ∘ i'

  module Iso∘-is-∘ {S T A B C}
                   (i : Iso S T A B) (i' : Iso A B A C) where
    i∘i' : Iso S T A C
    i∘i' = i ∘ i'

    i∘i'′ : Iso _ _ _ _
    i∘i'′ = i ∘ i'

anon : ∀ {A} (a : A) (p : A → Bool) {pa : T (p a)} → Iso′ (Maybe A) A
anon {A} a p = iso (maybe id a) go where
  go : A → Maybe A
  go x with p x
  ...     | true  = nothing
  ...     | false = just x

curried : ∀ {A} {B : A → _} {C : Σ A B → _}
            {D} {E : D → _} {F : Σ D E → _}
          → Iso (Π (Σ A B) C) (Π (Σ D E) F) (ΠΠ A B C) (ΠΠ D E F)
curried = iso curry uncurry

curried′ : ∀ {A B C D E F}
           → Iso (A × B → C) (D × E → F) (A → B → C) (D → E → F)
curried′ = curried

uncurried : ∀ {A} {B : A → _} {C : Σ A B → _}
              {D} {E : D → _} {F : Σ D E → _}
            → Iso (ΠΠ A B C) (ΠΠ D E F) (Π (Σ A B) C) (Π (Σ D E) F)
uncurried = iso uncurry curry

uncurried′ : ∀ {A B C D E F}
             → Iso (A → B → C) (D → E → F) (A × B → C) (D × E → F)
uncurried′ = uncurried
