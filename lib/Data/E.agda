{-# OPTIONS --type-in-type #-}
module Data.E where

open import Function
open import Data.Unit
open import Data.Empty
open import Data.Product
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

record Interface (In Out : Set) : Set where
  field
    E : Set → Set

  R : Set → Set
  R A = E A → A

  _≡E₁_ : Set → Set → Set₁
  -- _≡E₁_ A B = ∀ {P : Set → Set} → E (P A → P B)
  _≡E₁_ A B = E (A ≡ B)

  field
    pure : ∀ {A} → A → E A
    _=<<_ : ∀ {A B} → (A → E B) → E A → E B
    -- In≡Out : E (In ≡ Out)
    -- In≡Out : ∀ {P : Set → Set} → E (P In → P Out)
    In≡Out : In ≡E₁ Out
    rOut : R Out
    r⊥   : R ⊥

  infixl 4 _⊛_
  _>>=_ : ∀ {A B} → E A → (A → E B) → E B
  x >>= f = f =<< x
  _⟨$⟩_ : ∀ {A B} → (A → B) → E A → E B
  f ⟨$⟩ x = x >>= (pure ∘ f)
  _⊛_ : ∀ {A B} → E (A → B) → E A → E B
  f ⊛ x = f >>= λ f′ → f′ ⟨$⟩ x
  join : ∀ {A} → R (E A)
  join = _=<<_ id

  r⊤ : R ⊤
  r⊤ = _

  r→ : ∀ {A B} → R B → R (A → B)
  r→ rB f x = rB ((λ g → g x) ⟨$⟩ f)

  r× : ∀ {A B} → R A → R B → R (A × B)
  r× rA rB xy = rA (proj₁ ⟨$⟩ xy) , rB (proj₂ ⟨$⟩ xy)
  -- RΠ : ∀ {A} {B : A → Set} (rA : R A) → ((x : A) → B x) → ((ex : E A) → E (B (rA ex)))
  -- RΠ rA f ex = {!f ⊛ ex!}
  -- RΠ′  : ∀ {A} {B : E A → Set} → ((x : A) → B (pure x)) → ((ex : E A) → E (B ex))
  -- RΠ′ f ex = RΠ {B = λ x → ?} ? f ?

coe : ∀ {A B : Set} → A ≡ B → A → B
coe = ≡.subst id

record Laws {In Out} (r : Interface In Out) : Set where
  open Interface r
  field
    E≡id : E ≡ id

  id≡E = ≡.sym E≡id

  Id≡Pure : ∀ {A} → (A → A) ≡ (A → E A)
  Id≡Pure {A} = ≡.cong (λ e → A → e A) id≡E

  Id≡=<< : ∀ {A B} → ((A → B) → (A → B)) ≡ ((A → E B) → E A → E B)
  Id≡=<< {A} {B} = ≡.cong (λ e → (A → e B) → e A → e B) id≡E

  Id≡RA : ∀ {A} → (A → A) ≡ R A
  Id≡RA {A} = ≡.cong (λ e → e A → A) id≡E

  field
    pure≡id : ∀ {A} → pure {A} ≡ coe Id≡Pure id
    =<<≡id  : ∀ {A B} → _=<<_ {A} {B} ≡ coe Id≡=<< id
    rOut≡id : rOut ≡ coe Id≡RA id
    r⊥≡id   : r⊥ ≡ coe Id≡RA id

-- implem : ∀ {In Out} → In ≡ Out → Interface In Out
-- implem {In} {Out} eq = record {
implem : ∀ {A} → Interface A A
implem = record { E      = id;
                  pure   = id;
                  _=<<_  = id;
                  In≡Out = ≡.refl; -- id;
                  rOut   = id;
                  r⊥     = id
                }

module ELaws {A} where
  open Interface {A} implem
  laws : E (Laws {A} implem)
  laws = pure (record { E≡id = ≡.refl; pure≡id = ≡.refl; =<<≡id = ≡.refl; rOut≡id = ≡.refl; r⊥≡id = ≡.refl })

-- eLaws : ∀ {In Out} → Interface In Out → E (Laws )

open import Data.Nat
open import Function.NP      using (_∘_; _→⟨_⟩₁_; _$_) renaming (_→⟨_⟩₀_ to _→⟨_⟩_)

-- specialized version of _→⟨_⟩₀_ which helps inferring the arity
ℕ→⟨_⟩ℕ : ℕ → Set
ℕ→⟨ zero  ⟩ℕ = ℕ
ℕ→⟨ suc n ⟩ℕ = ℕ → ℕ→⟨ n ⟩ℕ

module Example {Out} (r : Interface ℕ Out) (elaws : Interface.E r (Laws r)) where
  open Interface r renaming (In≡Out to Eℕ≡O)

  ℕⁿ≡Oⁿ : ∀ n → (ℕ →⟨ n ⟩ ℕ) ≡E₁ (Out →⟨ n ⟩ Out)
  ℕⁿ≡Oⁿ n = ≡.cong P ⟨$⟩ Eℕ≡O
{-
  ℕⁿ≡Oⁿ n {Q} = ℕ≡O {Q ∘ P}
-}
     where P : Set → Set
           P A = A →⟨ n ⟩ A

  rOutⁿ : ∀ n → R (Out →⟨ n ⟩ Out)
  rOutⁿ zero    = rOut
  rOutⁿ (suc n) = r→ (rOutⁿ n)

  OEⁿ : ∀ n → E ((ℕ →⟨ n ⟩ ℕ) → (Out →⟨ n ⟩ Out))
  -- OEⁿ n = ℕⁿ≡Oⁿ n {id}
  OEⁿ n = ≡.subst id ⟨$⟩ ℕⁿ≡Oⁿ n

  Oⁿ : ∀ n → (ℕ →⟨ n ⟩ ℕ) → (Out →⟨ n ⟩ Out)
  Oⁿ n = r→ (rOutⁿ n) (OEⁿ n)

  0O = Oⁿ 0 0
  sucO = Oⁿ 1 suc
  _+O_ = Oⁿ 2 _+_
  _⊔O_ = Oⁿ 2 _⊔_

{-
  _O : ∀ {n} → (ℕ→⟨ n ⟩ℕ) → (Out →⟨ n ⟩ Out)
  _O {n} f = Oⁿ n (coe′ _ f)
    where coe′ : ∀ n → (ℕ→⟨ n ⟩ℕ) → (ℕ →⟨ n ⟩ ℕ)
          coe′ zero    = id
          coe′ (suc n) = λ f x → coe′ n (f x)

  0O = 0 O
  sucO = suc O
  _+O_ = _+_ O
  _⊔O_ = _⊔_ O
-}

  module Foo (laws : Laws r)
             where
    open Laws laws

    ℕ≡O : ℕ ≡ Out
    ℕ≡O = ≡.subst (λ e → e (ℕ ≡ Out)) E≡id Eℕ≡O

    ℕ→ℕ≡ℕ→O : (ℕ → ℕ) ≡ (ℕ → Out)
    ℕ→ℕ≡ℕ→O = ≡.cong (λ out → ℕ → out) ℕ≡O

    O≡ℕ = ≡.sym ℕ≡O

    Oⁿ0≡id : Oⁿ 0 ≡ coe ℕ→ℕ≡ℕ→O id
    Oⁿ0≡id = {!rOut≡id!}

    0O≡0 : 0O ≡ coe ℕ≡O 0
    0O≡0 = {!≡.subst !}

    0+n : ∀ {n} → 0O +O n ≡ n
    0+n {n} = {!!}

  -- Oⁿ≡id : ∀ n → E (pure (Oⁿ n) ≡ OEⁿ n)
  -- Oⁿ≡id n = ≡.cong {!!} ⟨$⟩ ℕ≡O

  -- O-sem : ∀ {arity} (f : ℕ → ℕ→⟨ arity ⟩ℕ) (x : ℕ) → E ((f O) (x O) ≡ (f x)O)
  -- O-sem {zero}  f x = {!!}
  -- O-sem {suc n} f x = {!!}
  -- O-sem : ∀ {arity} (f : ℕ → ℕ →⟨ arity ⟩ ℕ) (x : ℕ) → E ((Oⁿ (suc arity) f) (x O) ≡ Oⁿ arity (f x))
  -- O-sem : ∀ {arity} → E ((f : ℕ → ℕ →⟨ arity ⟩ ℕ) (x : ℕ) → (OEⁿ (suc arity) ⊛ pure f) ⊛ (OEⁿ 0 ⊛ pure x) ≡ OEⁿ arity ⊛ pure (f x))
  -- O-sem : ∀ {arity} → E ((f : ℕ → ℕ →⟨ arity ⟩ ℕ) (x : ℕ) → (Oⁿ (suc arity) f) (x O) ≡ Oⁿ arity (f x))
  -- O-sem = {!f x!}
