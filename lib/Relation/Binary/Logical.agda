{-# OPTIONS --without-K #-}
module Relation.Binary.Logical where

open import Type hiding (★)
open import Relation.Binary

open import Type.Param.Binary         public
open import Function.Param.Binary     public
open import Data.Zero.Param.Binary    public
open import Data.One.Param.Binary     public
open import Data.Two.Param.Binary     public
open import Data.Product.Param.Binary public
open import Data.Sum.Param.Binary     public
open import Data.Maybe.Param.Binary   public
open import Data.Dec.Param.Binary     public

open import Function.Equivalence
private
  ⟦→⟧⇔Preserves :
    ∀ {a b aᵣ bᵣ}
      {A : ★ a} {B : ★ b}
      {Aᵣ : ⟦★⟧ aᵣ A A}
      {Bᵣ : ⟦★⟧ bᵣ B B}
      {f}
    → (Aᵣ ⟦→⟧ Bᵣ) f f ⇔ f Preserves Aᵣ ⟶ Bᵣ

  ⟦→⟧⇔Preserves = equivalence (λ x → x) (λ x → x)

  ⟦→⟧²⇔Preserves₂ :
    ∀ {a b c aᵣ bᵣ cᵣ}
      {A : ★ a} {B : ★ b} {C : ★ c}
      {Aᵣ : ⟦★⟧ aᵣ A A}
      {Bᵣ : ⟦★⟧ bᵣ B B}
      {Cᵣ : ⟦★⟧ cᵣ C C}
      {f}
    → (Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ Cᵣ) f f ⇔ f Preserves₂ Aᵣ ⟶ Bᵣ ⟶ Cᵣ

  ⟦→⟧²⇔Preserves₂ = equivalence (λ f {x} {y}   {_} {_} z → f {x} {y} z)
                                (λ f {x} {y} z {_} {_}   → f z)

⟦Inj⟧ : ∀ {a₁ a₂ aᵣ} {A₁ : ★ a₁} {A₂ : ★ a₂} (Aᵣ : ⟦★⟧ aᵣ A₁ A₂)
          {b₁ b₂ bᵣ} {B₁ : ★ b₁} {B₂ : ★ b₂} (Bᵣ : ⟦★⟧ bᵣ B₁ B₂)
          (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → ★ _
⟦Inj⟧ Aᵣ Bᵣ f₁ f₂ = ∀ {x₁ x₂} (xᵣ : Bᵣ (f₁ x₁) (f₂ x₂)) → Aᵣ x₁ x₂

⟦Inj⟧′ : ∀ {a aᵣ} {A : ★ a} (Aᵣ : ⟦★⟧ aᵣ A A)
           {b bᵣ} {B : ★ b} (Bᵣ : ⟦★⟧ bᵣ B B)
           (f : A → B) → ★ _
⟦Inj⟧′ Aᵣ Bᵣ f = ⟦Inj⟧ Aᵣ Bᵣ f f
