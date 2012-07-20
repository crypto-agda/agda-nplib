{-# OPTIONS --universe-polymorphism #-}
module Data.Bool.NP where

open import Data.Bool using (Bool; true; false; T; if_then_else_; not)
import Algebra
import Data.Bool.Properties as B
open import Data.Unit using (⊤)
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.NP
open import Relation.Binary.Logical
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Relation.Binary.PropositionalEquality as ≡
import Function.Equivalence as E
open E.Equivalence using (to; from)
open import Function.Equality using (_⟨$⟩_)
open ≡ using (_≡_)

module Xor° = Algebra.CommutativeRing B.commutativeRing-xor-∧
module Bool° = Algebra.CommutativeSemiring B.commutativeSemiring-∧-∨

check : ∀ b → {pf : T b} → ⊤
check = _

If_then_else_ : ∀ {ℓ} {A B : Set ℓ} b → (T b → A) → (T (not b) → B) → if b then A else B
If_then_else_ true  x _ = x _
If_then_else_ false _ x = x _

If′_then_else_ : ∀ {ℓ} {A B : Set ℓ} b → A → B → if b then A else B
If′_then_else_ true  x _ = x
If′_then_else_ false _ x = x

If-map : ∀ {A B C D : Set} b (f : T b → A → C) (g : T (not b) → B → D) →
           if b then A else B → if b then C else D
If-map true  f _ = f _
If-map false _ f = f _

If-elim : ∀ {A B : Set} {P : Bool → Set}
            b (f : T b → A → P true) (g : T (not b) → B → P false) → if b then A else B → P b
If-elim true  f _ = f _
If-elim false _ f = f _

If-true : ∀ {A B : Set} {b} → T b → (if b then A else B) ≡ A
If-true {b = true}  _ = ≡.refl
If-true {b = false} ()

If-false : ∀ {A B : Set} {b} → T (not b) → (if b then A else B) ≡ B
If-false {b = true}  ()
If-false {b = false} _ = ≡.refl

cong-if : ∀ {A B : Set} b {t₀ t₁} (f : A → B) → (if b then f t₀ else f t₁) ≡ f (if b then t₀ else t₁)
cong-if true  _ = ≡.refl
cong-if false _ = ≡.refl

data ⟦Bool⟧ : (b₁ b₂ : Bool) → Set where
  ⟦true⟧   : ⟦Bool⟧ true true
  ⟦false⟧  : ⟦Bool⟧ false false

private
 module ⟦Bool⟧-Internals where
  refl : Reflexive ⟦Bool⟧
  refl {true}   = ⟦true⟧
  refl {false}  = ⟦false⟧

  sym : Symmetric ⟦Bool⟧
  sym ⟦true⟧  = ⟦true⟧
  sym ⟦false⟧ = ⟦false⟧

  trans : Transitive ⟦Bool⟧
  trans ⟦true⟧   = id
  trans ⟦false⟧  = id

  subst : ∀ {ℓ} → Substitutive ⟦Bool⟧ ℓ
  subst _ ⟦true⟧   = id
  subst _ ⟦false⟧  = id

  _≟_ : Decidable ⟦Bool⟧
  true   ≟  true   = yes ⟦true⟧
  false  ≟  false  = yes ⟦false⟧
  true   ≟  false  = no (λ())
  false  ≟  true   = no (λ())

  isEquivalence : IsEquivalence ⟦Bool⟧
  isEquivalence = record { refl = refl; sym = sym; trans = trans }

  isDecEquivalence : IsDecEquivalence ⟦Bool⟧
  isDecEquivalence = record { isEquivalence = isEquivalence; _≟_ = _≟_ }

  setoid : Setoid _ _
  setoid = record { Carrier = Bool; _≈_ = ⟦Bool⟧; isEquivalence = isEquivalence }

  decSetoid : DecSetoid _ _
  decSetoid = record { Carrier = Bool; _≈_ = ⟦Bool⟧; isDecEquivalence = isDecEquivalence }

  equality : Equality ⟦Bool⟧
  equality = record { isEquivalence = isEquivalence; subst = subst }

module ⟦Bool⟧-Props where
  open ⟦Bool⟧-Internals public using (subst; decSetoid; equality)
  open DecSetoid decSetoid public
  open Equality equality public hiding (subst; isEquivalence; refl; reflexive; sym; trans)

⟦if⟨_⟩_then_else_⟧ : ∀ {a₁ a₂ aᵣ} → (∀⟨ Aᵣ ∶ ⟦Set⟧ {a₁} {a₂} aᵣ ⟩⟦→⟧ ⟦Bool⟧ ⟦→⟧ Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ Aᵣ) if_then_else_ if_then_else_
⟦if⟨_⟩_then_else_⟧ _ ⟦true⟧  xᵣ _ = xᵣ
⟦if⟨_⟩_then_else_⟧ _ ⟦false⟧ _ xᵣ = xᵣ

⟦If′⟨_,_⟩_then_else_⟧ : ∀ {ℓ₁ ℓ₂ ℓᵣ} →
                       (∀⟨ Aᵣ ∶ ⟦Set⟧ {ℓ₁} {ℓ₂} ℓᵣ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦Set⟧ {ℓ₁} {ℓ₂} ℓᵣ ⟩⟦→⟧
                           ⟨ bᵣ ∶ ⟦Bool⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ ⟦if⟨ ⟦Set⟧ _ ⟩ bᵣ then Aᵣ else Bᵣ ⟧)
                       If′_then_else_ If′_then_else_
⟦If′⟨_,_⟩_then_else_⟧ _ _ ⟦true⟧  xᵣ _ = xᵣ
⟦If′⟨_,_⟩_then_else_⟧ _ _ ⟦false⟧ _ xᵣ = xᵣ

_==_ : (x y : Bool) → Bool
true == true = true
true == false = false
false == true = false
false == false = true

module == where
  _≈_ : (x y : Bool) → Set
  x ≈ y = T (x == y)

  refl : Reflexive _≈_
  refl {true}  = _
  refl {false} = _

  subst : ∀ {ℓ} → Substitutive _≈_ ℓ
  subst _ {true}   {true}   _ = id
  subst _ {false}  {false}  _ = id
  subst _ {true}   {false}  ()
  subst _ {false}  {true}   ()

  sym : Symmetric _≈_
  sym {x} {y} eq = subst (λ y → y ≈ x) {x} {y} eq (refl {x})

  trans : Transitive _≈_
  trans {x} {y} {z} x≈y y≈z = subst (_≈_ x) {y} {z} y≈z x≈y

  _≟_ : Decidable _≈_
  true   ≟  true   = yes _
  false  ≟  false  = yes _
  true   ≟  false  = no (λ())
  false  ≟  true   = no (λ())

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record { refl = λ {x} → refl {x}
                         ; sym = λ {x} {y} → sym {x} {y}
                         ; trans = λ {x} {y} {z} → trans {x} {y} {z} }

  isDecEquivalence : IsDecEquivalence _≈_
  isDecEquivalence = record { isEquivalence = isEquivalence; _≟_ = _≟_ }

  setoid : Setoid _ _
  setoid = record { Carrier = Bool; _≈_ = _≈_ ; isEquivalence = isEquivalence }

  decSetoid : DecSetoid _ _
  decSetoid = record { Carrier = Bool; _≈_ = _≈_; isDecEquivalence = isDecEquivalence }

module ⟦Bool⟧-Reasoning = Setoid-Reasoning ⟦Bool⟧-Props.setoid

open Data.Bool public

⟦true⟧′ : ∀ {b} → T b → ⟦Bool⟧ true b
⟦true⟧′ {true}  _ = ⟦true⟧
⟦true⟧′ {false} ()

⟦false⟧′ : ∀ {b} → T (not b) → ⟦Bool⟧ false b
⟦false⟧′ {true} ()
⟦false⟧′ {false} _ = ⟦false⟧

T∧ : ∀ {b₁ b₂} → T b₁ → T b₂ → T (b₁ ∧ b₂)
T∧ p q = _⟨$⟩_ (from B.T-∧) (p , q)

T∧₁ : ∀ {b₁ b₂} → T (b₁ ∧ b₂) → T b₁
T∧₁ = proj₁ ∘ _⟨$⟩_ (to B.T-∧)

T∧₂ : ∀ {b₁ b₂} → T (b₁ ∧ b₂) → T b₂
T∧₂ {b₁} = proj₂ ∘ _⟨$⟩_ (to (B.T-∧ {b₁}))

T∨'⊎ : ∀ {b₁ b₂} → T (b₁ ∨ b₂) → T b₁ ⊎ T b₂
T∨'⊎ {b₁} = _⟨$⟩_ (to (B.T-∨ {b₁}))

T∨₁ : ∀ {b₁ b₂} → T b₁ → T (b₁ ∨ b₂)
T∨₁ = _⟨$⟩_ (from B.T-∨) ∘ inj₁

T∨₂ : ∀ {b₁ b₂} → T b₂ → T (b₁ ∨ b₂)
T∨₂ {b₁} = _⟨$⟩_ (from (B.T-∨ {b₁})) ∘ inj₂

T'not'¬ : ∀ {b} → T (not b) → ¬ (T b)
T'not'¬ {false} _ = λ()
T'not'¬ {true} ()

T'¬'not : ∀ {b} → ¬ (T b) → T (not b)
T'¬'not {true}  f = f _
T'¬'not {false} _ = _

Tdec : ∀ b → Dec (T b)
Tdec true = yes _
Tdec false = no λ()

de-morgan : ∀ x y → not (x ∨ y) ≡ not x ∧ not y
de-morgan true  _ = ≡.refl
de-morgan false _ = ≡.refl
