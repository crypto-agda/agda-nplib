{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.Mixte where

import Category.Monad as Cat
open import Level
open import Function
open import Data.Nat hiding ({-_^_ ;-} _⊔_)
open import Data.List
open import Data.Empty
open import Data.Bool
open import Data.Unit
open import Data.Product
open import Data.Maybe.NP as Maybe
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.Bijection
open import Relation.Binary.Equivalence
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_;_≢_;_with-≡_)

{-
Note: there is some hope to extract from the result of the mixte logical relation some results
about the purely nominal one and the purely de Brujin one. However the results obtain about the
de Brujin relation may be reduced a bit. Indeed when a shadowing occurs on the nominal side, a
de Bruijn index is removed from the relation.
-}


shift : ∀ {a} {A : Set a} (x : A) → List (Maybe A) → List (Maybe A)
shift x xs = just x ∷ xs

_+/_ : ∀ {a} {A : Set a} (xs : List (Maybe A)) k → List (Maybe A)
xs +/ k = replicate k nothing ++ xs
infixl 5 _+/_

module +/-Props {a} {A : Set a} where
  +/-assoc : ∀ (xs : List (Maybe A)) k₁ k₂
             → xs +/ k₁ +/ k₂ ≡ xs +/ (k₂ + k₁)
  +/-assoc xs k₁ zero = ≡.refl
  +/-assoc xs k₁ (suc k₂) rewrite +/-assoc xs k₁ k₂ = ≡.refl

data _∷_^¹ {ℓ a} {A : Set a} (x : A) (α : REL ℕ A ℓ) : REL ℕ A (ℓ ⊔ a) where
  here   : (x ∷ α ^¹) 0 x
  there  : ∀ {i j}
             (αij :     α i j            )
             (x≢j :     x ≢ j            )
           →        --------------------
                    (x ∷ α ^¹) (suc i) j

{-
   x ∷ α ^¹ ≝ {(0,x)} ∪ {(i+1,y) | (i,y) ∈ α, x ≢ y}

   (x ∷ α ^¹) 0       y = x ≡ y
   (x ∷ α ^¹) (suc i) y = x ≢ y × α i y
 -}

toREL : ∀ {a} {A : Set a} → List (Maybe A) → REL ℕ A a
toREL []        _        = λ _ → Lift ⊥
toREL (x ∷ xs)  zero     = λ y → x ≡ just y
toREL (x ∷ xs)  (suc n)  = λ y → x ≢ just y × toREL xs n y

surjective : ∀ {a} {A : Set a} (xs : List (Maybe A)) → SurjectiveREL ℕ A (toREL xs)
surjective [] (lift ()) _
surjective (._ ∷ _) {._} {_} {zero}  ≡.refl  ≡.refl   = ≡.refl
surjective (_ ∷ vs) {_} {_}  {suc _} (_ , p) (_ , q)  = surjective vs p q

lookup : ∀ {a} {A : Set a} → List (Maybe A) → ℕ → Maybe A
lookup []        _        = nothing
lookup (x ∷ _)   zero     = x
lookup (x ∷ xs)  (suc n)  = lookup xs n

record MixteBij {a} (A : Set a) : Set a where
  constructor mb
  field
    items : List (Maybe A)
    items-injective : InjectiveREL ℕ A (toREL items)

  items-bijective : BijectiveREL ℕ A (toREL items)
  items-bijective = mkBijectiveREL items-injective (surjective items)

consMB : ∀ {a} {A : Set a} → Maybe A → MixteBij A → MixteBij A
consMB {A = A} mx (mb xs inj) = mb (mx ∷ xs) inj'
  where inj' : InjectiveREL ℕ A (toREL (mx ∷ xs))
        inj' {zero} {zero} _ _                = ≡.refl
        inj' {zero} {suc n} p (¬p , _)        = ⊥-elim (¬p p)
        inj' {suc n} {zero} (¬p , _) p        = ⊥-elim (¬p p)
        inj' {suc n} {suc n'} (_ , p) (_ , q) = ≡.cong suc (inj p q)

shiftMB : ∀ {a} {A : Set a} → A → MixteBij A → MixteBij A
shiftMB = consMB ∘ just

sucMB : ∀ {a} {A : Set a} → MixteBij A → MixteBij A
sucMB = consMB nothing

-- open Cat.RawMonad Maybe.monad

module Lookup-unsound where
  -- Here is a counter-example, that lookup is not always sound.
  A : Set
  A = ⊤
  xs : List (Maybe A)
  xs = just _ ∷ just _ ∷ []
  n : ℕ
  n = suc zero
  pf : ¬ (maybe (toREL xs n) ⊤ (lookup xs n))
  pf (neq , eq) = neq eq

  lookup-unsound : ¬(∀ {A : Set} (xs : List (Maybe A)) n
                     → maybe (toREL xs n) ⊤ (lookup xs n))
  lookup-unsound lookup-sound = pf (lookup-sound xs n)

lookup-complete : ∀ {a} {A : Set a} (xs : List (Maybe A)) n x
                  → toREL xs n x → maybe (_≡_ x) (Lift ⊤) (lookup xs n)
lookup-complete []            _       _  _       = _
lookup-complete (just .x ∷ _) zero    x  ≡.refl  = ≡.refl
lookup-complete (nothing ∷ _) zero    _  _       = _
lookup-complete (_ ∷ xs)      (suc n) y  (_ , r) = lookup-complete xs n y r

module WithEqDec {A : Set} (_≟_ : Decidable {A = A} _≡_) where
  open Cat.RawMonad Maybe.monad
  open DecSetoid (Maybe.decSetoid (≡.decSetoid _≟_)) renaming (_≟_ to _≟M_)

  index : List (Maybe A) → A → Maybe ℕ
  index [] _ = nothing
  index (x ∷ xs) y = if ⌊ x ≟M just y ⌋ then just zero else suc <$> index xs y

  cong-maybe : ∀ {A B : Set} (f : A → B) (x : A) y →
     maybe (_≡_ x) ⊤ y
     → maybe {A = B} (_≡_ (f x)) ⊤ (f <$> y)
  cong-maybe f _ (just _) = ≡.cong f
  cong-maybe f _ nothing  = id

  index-complete : ∀ (xs : List (Maybe A)) n y
                   → toREL xs n y → maybe (_≡_ n) ⊤ (index xs y)
  index-complete []        _        _  _                              = _
  index-complete (x ∷ _)   _        y  _      with x ≟M just y
  index-complete (_ ∷ _)   zero     _  _         | yes _              = ≡.refl
  index-complete (._ ∷ _)  (suc _)  _  (nq , _)  | yes (just ≡.refl)  = ⊥-elim (nq ≡.refl)
  index-complete (._ ∷ _)  zero     _  ≡.refl    | no nq              = ⊥-elim (nq refl)
  index-complete (x ∷ xs)  (suc n)  y  (_ , r)   | no _               = cong-maybe suc _ (index xs y) (index-complete xs n y r)

  index-sound : ∀ (xs : List (Maybe A)) y
                → maybe (flip (toREL xs) y) ⊤ (index xs y)
  index-sound [] _ = _
  index-sound (x ∷ xs) y with x ≟M just y
  index-sound (._ ∷ _) _ | yes (just ≡.refl) = ≡.refl
  ... | no neq with index-sound xs y | ≡.inspect (index xs y)
  ... | p | just i  with-≡ eq rewrite eq = (λ eq → neq (≡.subst (Eq _≡_ x) eq refl)) , p
  ... | p | nothing with-≡ eq rewrite eq = _

module shift⇔∷^¹ {a} {A : Set a} {x : A} (α : List (Maybe A)) where
  pf⇒ : x ∷ (toREL α) ^¹ ⇒ toREL (shift x α)
  pf⇒ here             = ≡.refl
  pf⇒ (there αij x≢j)  = x≢j ∘ just-injective , αij
  pf⇐ : toREL (shift x α) ⇒ x ∷ (toREL α) ^¹
  pf⇐ {zero}   ≡.refl     = here
  pf⇐ {suc _}  (x≢j , α)  = there α (x≢j ∘ ≡.cong just)
  proof : x ∷ (toREL α) ^¹ ⇔ toREL (shift x α)
  proof = equivalent pf⇒ pf⇐
