{- How this proof can be used for crypto, in particular ElGamal to DDH

  the Group A is ℤq with modular addition as operation
  the Group B is the cyclic group with order q

  φ is g^, the proof only need that it is a group homomorphism
  and that it has a right inverse

  we require that the explore (for type A) function (should work with only summation)
  is Stable under addition of A (notice that we have flip in there that is so that
  we don't need commutativity

  finally we require that the explore function respects extensionality

  This proof adds φ⁻¹ m, because adding a constant is stable under the
  big op F, this addition can then be pulled homomorphically through
  f, to become a, multiplication by m.
-}
open import Type using (Type_)
open import Level.NP
open import Function.NP
open import Relation.Binary.PropositionalEquality.NP
open ≡-Reasoning

module Algebra.Group.Isomorphism where

module M
  {a}{A  : Type a}
  {b}{B  : Type b}
  {c}{C  : Type c}
  (φ     : A → B)
  (φ⁻¹   : B → A)
  (φ-sur : ∀ {x} → φ (φ⁻¹ x) ≡ x)
  (_+_   : Op₂ A)
  (_*_   : Op₂ B)
  (φ-+-* : ∀ {x y} → φ (x + y) ≡ φ x * φ y)
  (F     : (A → B) → C)
  (F=    : ∀ {f g : A → B} → f ≗ g → F f ≡ F g)
  (Fφ+   : ∀ {k} → F φ ≡ F (φ ∘ _+_ k))
  {m     : B}
  where

  *-stable : F φ ≡ F (_*_ m ∘ φ)
  *-stable =
    F φ                  ≡⟨ Fφ+ ⟩
    F (φ ∘ _+_ (φ⁻¹ m))  ≡⟨ F= (λ x → φ (φ⁻¹ m + x)   ≡⟨ φ-+-* ⟩
                                       φ (φ⁻¹ m) * φ x ≡⟨ ap₂ _*_ φ-sur idp ⟩
                                       m * φ x         ∎) ⟩
    F (_*_ m ∘ φ)        ∎

open import Algebra.Group
open import Algebra.Group.Homomorphism

record GroupIsomorphism 
         {a}{A  : Type a}
         {b}{B  : Type b}
         (G+ : Group A)
         (G* : Group B)
          : Set(a ⊔ b) where
  open Additive-Group G+
  open Multiplicative-Group G*

  field
    φ : A → B -- TODO
    -- hom : GroupHomomorphism G+ G* φ
    φ-+-* : ∀ {x y} → φ (x + y) ≡ φ x * φ y
    φ⁻¹   : B → A
    φ-sur : ∀ {x} → φ (φ⁻¹ x) ≡ x
    -- φ-inj

module N
  {a}{A  : Type a}
  {b}{B  : Type b}
  {c}{C  : Type c}
  (G+ : Group A)
  (G* : Group B)
  (φ-iso : GroupIsomorphism G+ G*)
  (open Additive-Group G+)
  (open Multiplicative-Group G*)
  (open GroupIsomorphism φ-iso)
  (F     : (A → B) → C)
  (F=    : ∀ {f g : A → B} → f ≗ g → F f ≡ F g)
  (F+    : ∀ {k φ} → F φ ≡ F (φ ∘ _+_ k))
  {m     : B}
  where

  *-stable : F φ ≡ F (_*_ m ∘ φ)
  *-stable =
    F φ                  ≡⟨ F+ ⟩
    F (φ ∘ _+_ (φ⁻¹ m))  ≡⟨ F= (λ x → φ (φ⁻¹ m + x)   ≡⟨ φ-+-* ⟩
                                       φ (φ⁻¹ m) * φ x ≡⟨ ap₂ _*_ φ-sur idp ⟩
                                       m * φ x         ∎) ⟩
    F (_*_ m ∘ φ)        ∎

-- -}
-- -}
-- -}
-- -}
