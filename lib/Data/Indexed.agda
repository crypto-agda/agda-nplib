{-# OPTIONS --universe-polymorphism #-}

open import Level      using (_⊔_; suc; Level)
open import Function   using (id; const; _∘_; _∘′_; _ˢ_)
open import Data.Sum   using (_⊎_; inj₁; inj₂)
open import Data.Bool  using (Bool; true; false)
open import Data.Unit  using (⊤)
open import Data.List  using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Empty using (⊥)
open import Data.Product.NP using (∃; _,_; _×_)

module Data.Indexed {i} {Ix : Set i} where

|Set| : ∀ ℓ → Set _
|Set| ℓ = Ix → Set ℓ

|Set₀| : Set _
|Set₀| = Ix → Set

|Set₁| : Set _
|Set₁| = Ix → Set₂

|∀| : ∀ {f} (F : |Set| f) → Set _
|∀| F = ∀ {x} → F x

|∃| : ∀ {f} (F : |Set| f) → Set _
|∃| F = ∃[ x ] F x

|pure| : ∀ {a} {A : Set a} → A → (Ix → A)
|pure| = const

-- an alias for |pure|
|K| : ∀ {a} (A : Set a) → |Set| _
|K| = |pure|

|Cmp| : (F : |Set| _) (i j : Ix) → Set
|Cmp| F i j = F i → F j → Bool

|Π| : ∀ {f g} (F : |Set| f) (G : ∀ {i} → F i → |Set| g) → |Set| _
|Π| F G i = (x : F i) → G x i

-- this version used to work (type-checking its uses) better than that
infixr 0 _|→|_
_|→|_ : ∀ {f g} (F : |Set| f) (G : |Set| g) → |Set| (f ⊔ g)
F |→| G = |Π| F (const G)
-- expanded: (F |→| G) i = F i → G i

infixr 0 _|↦|_
_|↦|_ : ∀ {f g} (F : |Set| f) (G : |Set| g) → Set _
(F |↦| G) = |∀|(F |→| G)

|id| : ∀ {f} {F : |Set| f} → F |↦| F
|id| = id

_|∘|_ : ∀ {f g h} {F : |Set| f} {G : |Set| g} {H : |Set| h} → G |↦| H → F |↦| G → F |↦| H
f |∘| g = f ∘ g

infixr 0 _|$|_ _|$′|_

_|$|_ : ∀ {f g} {F : |Set| f} {G : ∀ {i} → F i → |Set| g}
        → |Π| F G |↦| |Π| F G
_|$|_ = id

_|$′|_ : ∀ {f g} {F : |Set| f} {G : |Set| g}
        → |∀| ((F |→| G) |→| F |→| G)
_|$′|_ = id

infixl 4 _|⊛|_

_|⊛|_ : ∀ {a b} {A : Set a} {B : Set b}
         → (Ix → A → B) → ((Ix → A) → (Ix → B))
_|⊛|_ = _ˢ_

|liftA| : ∀ {a b} {A : Set a} {B : Set b}
          → (A → B) → ((Ix → A) → (Ix → B))
-- |liftA| f x = |pure| f |⊛| x
|liftA| = _∘′_

|liftA2| : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
           → (A → B → C)
           → ((Ix → A) → (Ix → B) → (Ix → C))
|liftA2| f x y = |pure| f |⊛| x |⊛| y

|List| : ∀ {a} → |Set| a → |Set| a
|List| = |liftA| List

|[]| : ∀ {f} {F : |Set| f} → |∀|(|List| {f} F) -- Agda could not infer this {f}
|[]| = []

_|∷|_ : ∀ {f} {F : |Set| f}
         → |∀|(F |→| |List| F |→| |List| F)
_|∷|_ = _∷_

|Maybe| : ∀ {a} → |Set| a → |Set| a
|Maybe| = |liftA| Maybe

|nothing| : ∀ {f} {F : |Set| f} → |∀|(|Maybe| {f} F) -- Agda could not infer this {f}
|nothing| = nothing

|just| : ∀ {f} {F : |Set| f} → |∀|(F |→| |Maybe| F)
|just| = just

infixr 2 _|×|_
_|×|_ : ∀ {f g} (F : |Set| f) (G : |Set| g) → |Set| _
_|×|_ = |liftA2| _×_
-- or alternatively:
-- (F |×| G) i = F i × G i

_|,|_ : ∀ {f g} {F : |Set| f} {G : |Set| g} → |∀| (F |→| G |→| F |×| G)
_|,|_ = _,_

pack : ∀ {f} {F : |Set| f} → (x : Ix) → F x → |∃| F
pack = _,_

infixr 1 _|⊎|_

_|⊎|_ : ∀ {f g} (F : |Set| f) (G : |Set| g) → |Set| _
_|⊎|_ = |liftA2| _⊎_

|inj₁| : ∀ {f g} {F : |Set| f} {G : |Set| g} → F |↦| F |⊎| G
|inj₁| = inj₁

|inj₂| : ∀ {f g} {F : |Set| f} {G : |Set| g} → G |↦| F |⊎| G
|inj₂| = inj₂

|⊤| : |Set| _
|⊤| = |pure| ⊤

|⊥| : |Set| _
|⊥| = |pure| ⊥

|¬| : ∀ {ℓ} → |Set| ℓ → |Set| _
-- Agda was accepting it previously
-- |¬| F = F |→| |⊥|
|¬| F = λ i → (F |→| |⊥|) i

-- This is the type of |map| functions, the fmap function on Ix-indexed
-- functors.
|Map| : ∀ {a a' b b'} (F : |Set| a → |Set| a')
                      (G : |Set| b → |Set| b') → Set _
|Map| F G = ∀ {A B} → (A |↦| B) → F A |↦| G B

|map|-|K| : ∀ {a a' b b'}
              {F : Set a → Set a'}
              {G : Set b → Set b'}
              (fmap : ∀ {A B} → (A → B) → F A → G B)
              {A B} → (|K| A |↦| |K| B) → |K| (F A) |↦| |K| (G B)
|map|-|K| fmap f {i} x = fmap (f {i}) x
