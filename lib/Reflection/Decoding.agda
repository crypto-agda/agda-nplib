{-# OPTIONS --without-K #-}
open import Type
open import Reflection.NP
open import Data.Maybe
open import Data.Nat
open import Data.List as L
open import Data.Vec hiding (_>>=_;_⊛_)
open import Data.Product
open import Data.Bool
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Level.NP
import Category.Monad as Cat

module Reflection.Decoding where

module M? = Cat.RawMonad (Data.Maybe.monad {₀})
open M? using () renaming (_⊛_ to _⊛?_)

D : ★ → ★
D A = Term → Maybe A

pureD : ∀ {A} → A → D A
pureD a _ = just a

infixr 5 _⟨|⟩_
_⟨|⟩_ : ∀ {A} → (f g : D A) → D A
_⟨|⟩_ f g t = maybe′ just (g t) (f t)

emptyD : ∀ {A} → D A
emptyD _ = nothing

manyD : ∀ {A} → List (D A) → D A
manyD = L.foldr _⟨|⟩_ emptyD

mapD : ∀ {A B} → (A → B) → D A → D B
mapD f da = maybe′ (just ∘ f) nothing ∘ da

joinD : ∀ {A} → D (D A) → D A
joinD dda t = maybe′ (λ f → f t) nothing (dda t)

_>>=_ : ∀ {A B} → D A → (A → D B) → D B
_>>=_ da f t with da t
... | just a  = f a t
... | nothing = nothing

_=<<_ : ∀ {A B} → (A → D B) → D A → D B
_=<<_ f da = da >>= f

infixl 4 _⊛D_
_⊛D_ : ∀ {A B} → D (A → B) → D A → D B
_⊛D_ df da = df >>= λ f → da >>= λ a → pureD (f a)

ArgSpec : ★
ArgSpec = Implicit? × Relevant?

ArgSpecs : ★
ArgSpecs = List ArgSpec

deArg : ArgSpec → Arg Term → Maybe Term
deArg (im? , r?) (arg im?′ r?′ t) =
  if ⌊ im? ≟-Implicit? im?′ ⌋ ∧ ⌊ r? ≟-Relevant? r?′ ⌋ then just t else nothing

deArgs : (argSpecs : ArgSpecs) → Args → Maybe (Vec Term (length argSpecs))
deArgs []       []       = just []
deArgs (x ∷ xs) (y ∷ ys) = just _∷_ ⊛? deArg x y ⊛? deArgs xs ys
deArgs []       (_ ∷ _)  = nothing
deArgs (_ ∷ _)  []       = nothing

deCon : Name → (argSpecs : ArgSpecs) → D (Vec Term (length argSpecs))
deCon nm argSpecs (con nm′ args) =
  if nm == nm′ then deArgs argSpecs args else nothing
deCon _ _ _ = nothing

deDef : Name → (argSpecs : ArgSpecs) → D (Vec Term (length argSpecs))
deDef nm argSpecs (def nm′ args) =
  if nm == nm′ then deArgs argSpecs args else nothing
deDef _ _ _ = nothing
