module Function.Bijection.SyntaxKit where

import Level as L
open import Function.NP
open import Data.Bool
open import Data.Bool.Properties
open import Data.Unit
open import Relation.Binary.PropositionalEquality

record BijKit b {a} (A : Set a) : Set (L.suc b L.⊔ a) where
  constructor mk
  field
    Bij   : Set b
    eval  : Bij → Endo A
    _⁻¹   : Endo Bij
    idBij : Bij
    _⁏Bij_ : Bij → Bij → Bij

  eval⁻¹ : Bij → Endo A
  eval⁻¹ f = eval (f ⁻¹)

  _≗Bij_ : Bij → Bij → Set _
  _≗Bij_ = λ f g → ∀ (x : A) → eval f x ≡ eval g x

  field
    id-spec : eval idBij ≗ id
    _⁏-spec_ : ∀ f g → eval (f ⁏Bij g) ≗ eval g ∘ eval f

    _⁻¹-inverse : ∀ f → eval (f ⁻¹) ∘ eval f ≗ id
    _⁻¹-involutive : ∀ f → (f ⁻¹) ⁻¹ ≗Bij f

  _⁻¹-inverseBij : ∀ f → (f ⁏Bij f ⁻¹) ≗Bij idBij
  (f ⁻¹-inverseBij) x rewrite (f ⁏-spec (f ⁻¹)) x
                            | id-spec x
                            | (f ⁻¹-inverse)
                            x = refl

  _⁻¹-inverse′ : ∀ f → (eval f ∘ eval (f ⁻¹)) ≗ id
  (f ⁻¹-inverse′) x with ((f ⁻¹) ⁻¹-inverse) x
  ... | p rewrite (f ⁻¹-involutive) (eval (f ⁻¹) x) = p

  _⁻¹-inverseBij′ : ∀ f → (f ⁻¹ ⁏Bij f) ≗Bij idBij
  (f ⁻¹-inverseBij′) x rewrite (f ⁻¹ ⁏-spec f) x
                             | id-spec x
                             | (f ⁻¹-inverse′)
                            x = refl

module BoolBijection where
  data BoolBij : Set where
    `id `not : BoolBij

  bool-bijKit : BijKit L.zero Bool
  bool-bijKit = mk BoolBij eval id `id _⁏Bij_ (λ _ → refl) _⁏-spec_ _⁻¹-inverse (λ _ _ → refl)
   module BBK where
    eval  : BoolBij → Endo Bool
    eval `id = id
    eval `not = not

    _⁏Bij_ : BoolBij → BoolBij → BoolBij
    `id  ⁏Bij g    = g
    f    ⁏Bij `id  = f
    `not ⁏Bij `not = `id

    _⁏-spec_ : ∀ f g → eval (f ⁏Bij g) ≗ eval g ∘ eval f
    `id  ⁏-spec g    = λ _ → refl
    `not ⁏-spec `id  = λ _ → refl
    `not ⁏-spec `not = sym ∘ not-involutive

    _⁻¹-inverse : ∀ f → eval f ∘ eval f ≗ id
    (`id  ⁻¹-inverse) = λ _ → refl
    (`not ⁻¹-inverse) = not-involutive

  module BoolBijKit = BijKit bool-bijKit

  -- `xor can be seen as a fromBool function
  `xor : Bool → BoolBij
  `xor false = `id
  `xor true  = `not

  -- `not? can be seen as a toBool function
  `not? : BoolBij → Bool
  `not? `id  = false
  `not? `not = true

  `xor∘`not? : `xor ∘ `not? ≗ id
  `xor∘`not? `id = refl
  `xor∘`not? `not = refl

  `not?∘`xor : `not? ∘ `xor ≗ id
  `not?∘`xor true  = refl
  `not?∘`xor false = refl

module 1-Bijection {a} (A : Set a) where
    1-bij : BijKit L.zero A
    1-bij = mk ⊤ (λ _ → id) _ _ _ (λ _ → refl) (λ _ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)

    module 1-BijKit = BijKit 1-bij

module UnitBijection where
    open 1-Bijection
    ⊤-bijKit : BijKit L.zero ⊤
    ⊤-bijKit = 1-bij ⊤

    module UnitBijKit = 1-BijKit ⊤
