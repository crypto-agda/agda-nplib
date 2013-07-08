module Function.Bijection.SyntaxKit where

open import Type hiding (★)
open import Level.NP using (₀; ₛ; _⊔_)
open import Function.NP
open import Data.One
open import Data.Two
open import Data.Bool.Properties
open import Relation.Binary.PropositionalEquality

record BijKit b {a} (A : ★ a) : ★ (ₛ b ⊔ a) where
  constructor mk
  field
    Bij   : ★ b
    eval  : Bij → Endo A
    _⁻¹   : Endo Bij
    idBij : Bij
    _⁏Bij_ : Bij → Bij → Bij

  eval⁻¹ : Bij → Endo A
  eval⁻¹ f = eval (f ⁻¹)

  _≗Bij_ : Bij → Bij → ★ _
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

module 𝟚Bijection where
  data 𝟚Bij : ★₀ where
    `id `not : 𝟚Bij

  bool-bijKit : BijKit ₀ 𝟚
  bool-bijKit = mk 𝟚Bij eval id `id _⁏Bij_ (λ _ → refl) _⁏-spec_ _⁻¹-inverse (λ _ _ → refl)
   module BBK where
    eval  : 𝟚Bij → Endo 𝟚
    eval `id = id
    eval `not = not

    _⁏Bij_ : 𝟚Bij → 𝟚Bij → 𝟚Bij
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

  module 𝟚BijKit = BijKit bool-bijKit

  -- `xor can be seen as a from𝟚 function
  `xor : 𝟚 → 𝟚Bij
  `xor 0₂ = `id
  `xor 1₂ = `not

  -- `not? can be seen as a to𝟚 function
  `not? : 𝟚Bij → 𝟚
  `not? `id  = 0₂
  `not? `not = 1₂

  `xor∘`not? : `xor ∘ `not? ≗ id
  `xor∘`not? `id = refl
  `xor∘`not? `not = refl

  `not?∘`xor : `not? ∘ `xor ≗ id
  `not?∘`xor 1₂ = refl
  `not?∘`xor 0₂ = refl

module 1-Bijection {a} (A : ★ a) where
    1-bij : BijKit ₀ A
    1-bij = mk 𝟙 (λ _ → id) _ _ _ (λ _ → refl) (λ _ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)

    module 1-BijKit = BijKit 1-bij

module 𝟙Bijection where
    open 1-Bijection
    𝟙-bijKit : BijKit ₀ 𝟙
    𝟙-bijKit = 1-bij 𝟙

    module 𝟙BijKit = 1-BijKit 𝟙
