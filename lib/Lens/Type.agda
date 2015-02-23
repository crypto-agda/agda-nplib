--TODO {-# OPTIONS --without-K #-}
-- Inspired from the haskell 'lens' package
module Lens.Type where

open import Level
open import Function.NP
open import Type
open import Category.Functor
open import Category.Applicative
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Binary.PropositionalEquality using (_≗_; _≡_; refl)

Overloading : (_↝₀_ _↝₁_ : ★ → ★ → ★) (F : ★ → ★) (S T A B : ★) → ★
Overloading _↝₀_ _↝₁_ F S T A B = A ↝₀ F B → S ↝₁ F T

LensLike : (F : ★ → ★) (S T A B : ★) → ★
LensLike = Overloading -→- -→-
-- alternatively
-- LensLike F S T A B = (A → F B) → S → F T

Simple : ∀ {f s a} (F : (S T : Set s) (A B : Set a) → Set f)
                   (S : Set s) (A : Set a) → Set f
Simple F S A = F S S A A

Overloading′ : (_↝₀_ _↝₁_ : ★ → ★ → ★) (F : ★ → ★) (S A : ★) → ★
Overloading′ _↝₀_ _↝₁_ F = Simple (Overloading _↝₀_ _↝₁_ F)

LensLike′ : (F : ★ → ★) (S A : ★) → ★
LensLike′ F = Simple (LensLike F)

Lens : (S T A B : ★) → ★₁
Lens S T A B = ∀ {F} {{Ffun : RawFunctor F}} → LensLike F S T A B

Lens′ : (S A : ★) → ★₁
Lens′ = Simple Lens

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

module ContextRawFunctorLaws {A B : ★} where
    map = RawFunctor._<$>_ (ContextRawFunctor {A} {B})
    private
      F = Context A B

    map-id : ∀ {T} → map id ≗ id {A = F T}
    map-id _ = refl

    map-∘ : ∀ {S T U} (f : T → U) (g : S → T) → map f ∘ map g ≗ map (f ∘ g)
    map-∘ f g x = refl

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

Loupe : (S T A B : ★) → ★
Loupe S T A B = LensLike (Context A B) S T A B

{-
-- This one is not an Endo functor because of predicativity
record Bazaar (A B T : ★) : ★₁ where
  constructor mk
  field
    run : ∀ {F : ★ → ★} {{F-app : RawApplicative F}} → (A → F B) → F T

bazaar : ∀ {A B T} {F : ★ → ★} {{F-app : RawApplicative F}}
         → (A → F B) → Bazaar A B T → F T
bazaar afb baz = Bazaar.run baz afb

sell : ∀ {A B} → A → Bazaar A B B
sell x = mk (λ f → f x)

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
-}

data Bazaar (A B T : ★) : ★ where
  buy   : T → Bazaar A B T
  trade : Bazaar A B (B → T) → A → Bazaar A B T

sell : ∀ {A B} → A → Bazaar A B B
sell = trade (buy id)

bazaar : ∀ {A B T} {F : ★ → ★} {{F-app : RawApplicative F}}
         → (A → F B) → Bazaar A B T → F T
bazaar afb (buy x)       = pure x                 where open RawApplicative {{...}}
bazaar afb (trade baz x) = bazaar afb baz ⊛ afb x where open RawApplicative {{...}}

private
    -- While reading: http://twanvl.nl/blog/haskell/non-regular1
    module BazaarMisc where
        open import Data.List.NP as List
        FunList = λ A B → Bazaar A A B

        getB : ∀ {A B} → FunList A B → B
        getB = bazaar {{id-app}} id

        getAs : ∀ {A B} → FunList A B → List A
        getAs (buy _)       = []
        getAs (trade baz x) = x ∷ getAs baz

BazaarRawApplicative : ∀ {A B : ★} → RawApplicative _
BazaarRawApplicative {A} {B} = record { pure = buy; _⊛_ = _⊛_ }
  where
    private
      F = Bazaar A B

    map : ∀ {S T} → (S → T) → F S → F T
    map f (buy x)      = buy (f x)
    map f (trade mx x) = trade (map (_∘_ f) mx) x

    map-id : ∀ {T} → map id ≗ id {A = F T}
    map-id (buy x)                      = refl
    map-id (trade m x) rewrite map-id m = refl

    map-∘ : ∀ {S T U} (f : T → U) (g : S → T) → map f ∘ map g ≗ map (f ∘ g)
    map-∘ f g (buy x) = refl
    map-∘ f g (trade m x) rewrite map-∘ (_∘_ f) (_∘_ g) m = refl

    map₂ : ∀ {S T U} → (S → T → U) → F S → F T → F U
    map₂ f (buy x)      my = map (f x) my
    map₂ f (trade mx x) my = trade (map₂ (λ g y → flip f y ∘ g) mx my) x

    infixl 4 _⊛_
    _⊛_ : ∀ {S T} → F (S → T) → F S → F T
    _⊛_ = map₂ id
    {- -- does not termination check
    buy f      ⊛ mx = map f mx
    trade mf x ⊛ mx = trade (map flip mf ⊛ mx) x
    -}

    identity : ∀ {T} (x : F T) → buy id ⊛ x ≡ x
    identity = map-id

    -- this one seems annoying
    -- composition : ∀ {R S T} (u : F (S → T)) (v : F (R → S)) (w : F R) → buy _∘′_ ⊛ u ⊛ v ⊛ w ≡ u ⊛ (v ⊛ w)

    homomorphism : ∀ {S T} (f : S → T) (x : S) → buy f ⊛ buy x ≡ buy (f x)
    homomorphism _ _ = refl

-- universe issue
-- BazaarFunctor : ∀ {A B} → RawFunctor (Bazaar A B)

record Exchange (R A B : ★) : ★ where
  constructor _,_
  field
    exchange : A → R
    extract  : B

open Exchange public using (exchange)

module Exchanges {R A} where
  private
    F = Exchange R A

  map : ∀ {B C} → (B → C) → F B → F C
  map f (ar , b) = ar , f b

  rawFunctor : RawFunctor F
  rawFunctor = record { _<$>_ = map }

  extract : ∀ {B} → F B → B
  extract = Exchange.extract

  duplicate : ∀ {B} → F B → F (F B)
  duplicate (ar , b) = ar , (ar , b)

choosing : ∀ {F S S′ T T′ A B} {{_ : RawFunctor F}} →
             LensLike F S T A B →
             LensLike F S′ T′ A B →
             LensLike F (S ⊎ S′) (T ⊎ T′) A B
choosing ℓ r f = [ _<$>_ inl ∘ ℓ f
                 , _<$>_ inr ∘ r f ]
  where open RawFunctor {{...}}

choosen : ∀ {A B} → Lens (A ⊎ A) (B ⊎ B) A B
choosen = choosing id id

inside : ∀ {S T A B E}
         → Loupe S T A B
         → Lens (E → S) (E → T) (E → A) (E → B)
inside ℓ f es = o <$> f i where
  open RawFunctor {{...}}
  open Context
  i = get ∘ ℓ (_,_ id) ∘ es
  o = λ ea e → set (ℓ (_,_ id) (es e)) (ea e)

alongside : ∀ {S S′ T T′ A A′ B B′}
            → Loupe S  T  A  B
            → Loupe S′ T′ A′ B′
            → Lens (S × S′) (T × T′) (A × A′) (B × B′)
alongside l r f (s , s′) = case l (_,_ id) s of λ
  { (bt , a) → case r (_,_ id) s′ of λ
                 { (bt′ , a′) → f (a , a′) <&> λ { (b , b′) → (bt b , bt′ b′) }
                 } }
                  where _<&>_ = flip (RawFunctor._<$>_ it)

cloneLens : ∀ {S T A B} → Loupe S T A B → Lens S T A B
cloneLens f afb s = case f (_,_ id) s of λ { (bt , a) → bt <$> afb a }
  where open RawFunctor {{...}}
-- -}
