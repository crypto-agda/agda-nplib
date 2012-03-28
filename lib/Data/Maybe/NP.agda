{-# OPTIONS --universe-polymorphism #-}
module Data.Maybe.NP where

open import Function
import Level as L
open L using (_⊔_; lift)
open import Data.Maybe public
open import Category.Applicative
import      Category.Monad as Cat
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_;_≗_)
open import Relation.Binary.Logical
open import Function using (type-signature;_$_;flip;id)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; zero; suc)

module M? ℓ where
  open Cat.RawMonad (monad {ℓ}) public

Π? : ∀ {a b} (A : Set a) (B : A → Set b) → Set _
Π? A B = (x : A) → Maybe (B x)

_→?_ : ∀ {a b} → Set a → Set b → Set _
A →? B = A → Maybe B

map? : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
map? f = maybe (just ∘′ f) nothing
-- map? = M?._<$>_ _ <= not universe-polymorphic enough

-- more universe-polymorphic than M?.join
join? : ∀ {a} {A : Set a} → Maybe (Maybe A) → Maybe A
join? nothing  = nothing
join? (just x) = x

Maybe^ : ℕ → Set → Set
Maybe^ zero    = id
Maybe^ (suc n) = Maybe ∘ Maybe^ n

just-injective : ∀ {a} {A : Set a} {x y : A}
                 → (just x ∶ Maybe A) ≡ just y → x ≡ y
just-injective ≡.refl = ≡.refl

maybe-just-nothing : ∀ {a} {A : Set a} → maybe {A = A} just nothing ≗ id
maybe-just-nothing (just _)  = ≡.refl
maybe-just-nothing nothing   = ≡.refl

applicative : ∀ {f} → RawApplicative {f} Maybe
applicative = record { pure = just ; _⊛_  = _⊛_ }
  where
    _⊛_ : ∀ {a b}{A : Set a}{B : Set b} → Maybe (A → B) → Maybe A → Maybe B
    just f  ⊛ just x = just (f x)
    _       ⊛ _      = nothing

just? : ∀ {a} {A : Set a} → Maybe A → Set
just? nothing  = ⊥
just? (just _) = ⊤

data ⟦Maybe⟧ {a b r} {A : Set a} {B : Set b} (_∼_ : A → B → Set r) : Maybe A → Maybe B → Set (a ⊔ b ⊔ r) where
  ⟦just⟧ : ∀ {x₁ x₂} → (xᵣ : x₁ ∼ x₂) → ⟦Maybe⟧ _∼_ (just x₁) (just x₂)
  ⟦nothing⟧ : ⟦Maybe⟧ _∼_ nothing nothing

⟦maybe⟧ : ∀ {a b} → (∀⟨ Aᵣ ∶ ⟦Set⟧ a ⟩⟦→⟧ (∀⟨ Bᵣ ∶ ⟦Set⟧ b ⟩⟦→⟧ ((Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ (Bᵣ ⟦→⟧ (⟦Maybe⟧ Aᵣ ⟦→⟧ Bᵣ)))))
                     (maybe {a} {b}) (maybe {a} {b})
⟦maybe⟧ _ _ justᵣ nothingᵣ (⟦just⟧ xᵣ) = justᵣ xᵣ
⟦maybe⟧ _ _ justᵣ nothingᵣ ⟦nothing⟧   = nothingᵣ

_⟦→?⟧_ : ∀ {a b c d} → (⟦Set⟧ {a} {b} c ⟦→⟧ ⟦Set⟧ {a} {b} d ⟦→⟧ ⟦Set⟧ _) _→?_ _→?_
Aᵣ ⟦→?⟧ Bᵣ = Aᵣ ⟦→⟧ ⟦Maybe⟧ Bᵣ

module ⟦Maybe⟧-Properties where

  refl : ∀ {a} {A : Set a} {_∼_ : A → A → Set} (refl-A : ∀ x → x ∼ x) (mx : Maybe A) → ⟦Maybe⟧ _∼_ mx mx
  refl refl-A (just x) = ⟦just⟧ (refl-A x)
  refl refl-A nothing = ⟦nothing⟧

  sym : ∀ {a b} {A : Set a} {B : Set b} {_∼₁_ : A → B → Set} {_∼₂_ : B → A → Set}
          (sym-AB : ∀ {x y} → x ∼₁ y → y ∼₂ x) {mx : Maybe A} {my : Maybe B}
        → ⟦Maybe⟧ _∼₁_ mx my → ⟦Maybe⟧ _∼₂_ my mx
  sym sym-A (⟦just⟧ x∼₁y) = ⟦just⟧ (sym-A x∼₁y)
  sym sym-A ⟦nothing⟧ = ⟦nothing⟧

  trans : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
            {_⟦AB⟧_ : A → B → Set}
            {_⟦BC⟧_ : B → C → Set}
            {_⟦AC⟧_ : A → C → Set}
            (trans : ∀ {x y z} → x ⟦AB⟧ y → y ⟦BC⟧ z → x ⟦AC⟧ z)
            {mx : Maybe A} {my : Maybe B} {mz : Maybe C}
          → ⟦Maybe⟧ _⟦AB⟧_ mx my → ⟦Maybe⟧ _⟦BC⟧_ my mz
          → ⟦Maybe⟧ _⟦AC⟧_ mx mz
  trans trans' (⟦just⟧ x∼y) (⟦just⟧ y∼z) = ⟦just⟧ (trans' x∼y y∼z)
  trans trans' ⟦nothing⟧ ⟦nothing⟧ = ⟦nothing⟧

  subst-⟦AB⟧ : ∀ {a b} {A : Set a} {B : Set b}
                 (P : Maybe A → Set)
                 (Q : Maybe B → Set)
                 (⟦AB⟧ : A → B → Set)
                 (subst-⟦AB⟧ : ∀ {x y} → ⟦AB⟧ x y → P (just x) → Q (just y))
                 (Pnothing→Qnothing : P nothing → Q nothing)
                 {mx : Maybe A} {my : Maybe B}
               → (⟦Maybe⟧ ⟦AB⟧ mx my) → P mx → Q my
  subst-⟦AB⟧ _ _ _ subst-⟦AB⟧ _ (⟦just⟧ x∼y) Pmx = subst-⟦AB⟧ x∼y Pmx
  subst-⟦AB⟧ _ _ _ _          f ⟦nothing⟧    Pnothing = f Pnothing

  subst : ∀ {a} {A : Set a}
            (P : Maybe A → Set)
            (Aᵣ : A → A → Set)
            (subst-Aᵣ : ∀ {x y} → Aᵣ x y → P (just x) → P (just y))
            {mx my}
          → (⟦Maybe⟧ Aᵣ mx my) → P mx → P my
  subst P Aᵣ subst-Aᵣ = subst-⟦AB⟧ P P Aᵣ subst-Aᵣ id

IsNothing'≡nothing : ∀ {a} {A : Set a} {x : Maybe A} → IsNothing x → x ≡ nothing
IsNothing'≡nothing nothing = ≡.refl
IsNothing'≡nothing (just (lift ()))

≡nothing'IsNothing : ∀ {a} {A : Set a} {x : Maybe A} → x ≡ nothing → IsNothing x
≡nothing'IsNothing ≡.refl = nothing

_≡JAll_ : ∀ {a} {A : Set a} (x y : Maybe A) → Set a
x ≡JAll y = All (λ y' → All (_≡_ y') y) x

_≡JAny_ : ∀ {a} {A : Set a} (x y : Maybe A) → Set a
x ≡JAny y = Any (λ y' → Any (_≡_ y') y) x

module MonadLemmas where

  open M? L.zero public
 --  open RawApplicative applicative public
  cong-Maybe : ∀ {A B : Set}
  -- cong-Maybe : ∀ {a b} {A : Set a} {B : Set b}
                 (f : A → B) {x y} → x ≡ pure y → f <$> x ≡ pure (f y)
  cong-Maybe f ≡.refl = ≡.refl

  cong₂-Maybe : ∀ {A B C : Set}
               (f : A → B → C) {x y u v} → x ≡ pure y → u ≡ pure v → pure f ⊛ x ⊛ u ≡ pure (f y v)
  cong₂-Maybe f ≡.refl ≡.refl = ≡.refl

  Maybe-comm-monad :
    ∀ {A B C} {x y} {f : A → B → Maybe C} →
      (x >>= λ x' → y >>= λ y' → f x' y')
    ≡ (y >>= λ y' → x >>= λ x' → f x' y')
  Maybe-comm-monad {x = nothing} {nothing}  = ≡.refl
  Maybe-comm-monad {x = nothing} {just _}   = ≡.refl
  Maybe-comm-monad {x = just _}  {nothing}  = ≡.refl
  Maybe-comm-monad {x = just _}  {just _}   = ≡.refl

  Maybe-comm-appl : ∀ {A B} {f : Maybe (A → B)} {x} → f ⊛ x ≡ (flip _$_) <$> x ⊛ f
  Maybe-comm-appl {f = nothing} {nothing}  = ≡.refl
  Maybe-comm-appl {f = nothing} {just _}   = ≡.refl
  Maybe-comm-appl {f = just _}  {nothing}  = ≡.refl
  Maybe-comm-appl {f = just _}  {just _}   = ≡.refl

  Maybe-comm-appl₂ : ∀ {A B C} {f : A → B → C} {x y} → f <$> x ⊛ y ≡ flip f <$> y ⊛ x
  Maybe-comm-appl₂ {x = nothing} {nothing}  = ≡.refl
  Maybe-comm-appl₂ {x = nothing} {just _}   = ≡.refl
  Maybe-comm-appl₂ {x = just _}  {nothing}  = ≡.refl
  Maybe-comm-appl₂ {x = just _}  {just _}   = ≡.refl

module FunctorLemmas where
  open M? L.zero

  <$>-injective₁ : ∀ {A B : Set}
                     {f : A → B} {x y : Maybe A}
                     (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y)
                   → f <$> x ≡ f <$> y → x ≡ y
  <$>-injective₁ {x = just _}  {just _}  f-inj eq = ≡.cong just (f-inj (just-injective eq))
  <$>-injective₁ {x = nothing} {nothing} _     _  = ≡.refl
  <$>-injective₁ {x = just _}  {nothing} _     ()
  <$>-injective₁ {x = nothing} {just _}  _     ()

  <$>-assoc : ∀ {A B C : Set} {f : A → B} {g : C → A} (x : Maybe C) → f ∘ g <$> x ≡ f <$> (g <$> x)
  <$>-assoc (just _) = ≡.refl
  <$>-assoc nothing  = ≡.refl
