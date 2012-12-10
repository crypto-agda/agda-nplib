-- Inspired from the haskell 'lens' package
module Lens.Type where

open import Level
open import Function.NP
open import Type
open import Category.Functor
open import Category.Applicative
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])

Simple : ∀ {f s a} (F : (S T : Set s) (A B : Set a) → Set f)
                   (S : Set s) (A : Set a) → Set f
Simple F S A = F S S A A

LensLike : (F : ★ → ★) (S T A B : ★) → ★
LensLike F S T A B = (A → F B) → S → F T

SimpleLensLike : (F : ★ → ★) (S A : ★) → ★
SimpleLensLike F = Simple (LensLike F)

Lens : (S T A B : ★) → ★₁
Lens S T A B = ∀ {F} {{Ffun : RawFunctor F}} → LensLike F S T A B

SimpleLens : (S A : ★) → ★₁
SimpleLens = Simple Lens

lens : ∀ {S T A B} → (S → A) → (S → B → T) → Lens S T A B
lens sa sbt afb s = sbt s <$> afb (sa s)
  where open RawFunctor {{...}}

record Context (A B T : ★) : ★ where
  constructor _,_
  field
    set : B → T
    get : A

ContextRawFunctor : ∀ {A B} → RawFunctor (Context A B)
ContextRawFunctor
  = record { _<$>_ = λ { f (s , g) → (f ∘ s) , g } }

module ContextComonad {A : ★} where
  private
    W = Context A A

  extract : ∀ {T} → W T → T
  extract (s , g) = s g

  duplicate : ∀ {T} → W T → W (W T)
  duplicate (s , g) = _,_ s , g

  extend : ∀ {T U} → (W T → U) → W T → W U
  extend f (s , g) = (f ∘ _,_ s) , g
  -- ComonadStore...

record Bazaar (A B T : ★) : ★₁ where
  constructor mk
  field
    run : ∀ {F : ★ → ★} {{F-app : RawApplicative F}} → (A → F B) → F T

bazaar : ∀ {A B T} {F : ★ → ★} {{F-app : RawApplicative F}}
         → (A → F B) → Bazaar A B T → F T
bazaar afb baz = Bazaar.run baz afb

{-
sell : ∀ {A B} → A → Bazaar A B B
sell x = {!!}
-}

module BazaarApplicative {A B : ★} where
  module A = RawApplicative {{...}}
  private
    F = Bazaar A B

  map : ∀ {S T} → (S → T) → F S → F T
  map f (mk m) = mk (A._<$>_ f ∘ m)

  pure : ∀ {T} → T → F T
  pure x = mk (λ k → A.pure x)

  _⊛_ : ∀ {S T} → F (S → T) → F S → F T
  mk mf ⊛ mk mx = mk (λ k → mf k A.⊛ mx k)

-- universe issue
-- BazaarFunctor : ∀ {A B} → RawFunctor (Bazaar A B)

module BazaarComonad {A : ★} where
  private
    W = Bazaar A A

  extract : ∀ {T} → W T → T
  extract (mk m) = m {id} {{id-app}} id

  -- duplicate : ∀ {T} → W T → W (W T)
  -- duplicate (mk m) = 

  {-
  extend : ∀ {T U} → (W T → U) → W T → W U
  extend f m = {!!}
  -}

choosing : ∀ {F S S′ T T′ A B} {{_ : RawFunctor F}} →
             LensLike F S T A B →
             LensLike F S′ T′ A B →
             LensLike F (S ⊎ S′) (T ⊎ T′) A B
choosing ℓ r f = [ _<$>_ inj₁ ∘ ℓ f
                 , _<$>_ inj₂ ∘ r f ]
  where open RawFunctor {{...}}

choosen : ∀ {A B} → Lens (A ⊎ A) (B ⊎ B) A B
choosen = choosing id id

inside : ∀ {S T A B E} →
           LensLike (Context A B) S T A B → Lens (E → S) (E → T) (E → A) (E → B)
inside ℓ f es = o <$> f i where
  open RawFunctor {{...}}
  open Context
  i = get ∘ ℓ (_,_ id) ∘ es
  o = λ ea e → set (ℓ (_,_ id) (es e)) (ea e)

alongside : ∀ {S S′ T T′ A A′ B B′}
            → LensLike (Context A B) S T A B
            → LensLike (Context A′ B′)  S′ T′ A′ B′
            → Lens (S × S′) (T × T′) (A × A′) (B × B′)
alongside l r f (s , s′) = case l (_,_ id) s of λ
  { (bt , a) → case r (_,_ id) s′ of λ
                 { (bt′ , a′) → f (a , a′) <&> λ { (b , b′) → (bt b , bt′ b′) }
                 } }
                  where _<&>_ = flip (RawFunctor._<$>_ …)
