{-# OPTIONS --universe-polymorphism #-}
module Data.Bool.NP where

open import Type hiding (★)
open import Data.Bool using (Bool; true; false; T; if_then_else_; not)
import Algebra
open import Algebra.FunctionProperties using (Op₁; Op₂)
import Data.Bool.Properties as B
open import Data.Unit using (⊤)
open import Data.Product
open import Data.Sum
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s; _⊓_; _⊔_; _∸_)
open import Function.NP
open import Relation.Binary.NP
open import Relation.Binary.Logical
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Relation.Binary.PropositionalEquality as ≡
import Function.Equivalence as E
open E.Equivalence using (to; from)
open import Function.Equality using (_⟨$⟩_)
open ≡ using (_≡_)

cond : ∀ {a} {A : ★ a} → A → A → Bool → A
cond x y b = if b then x else y

Cond : ∀ {ℓ} {A B : ★ ℓ} → A → B → (b : Bool) → cond A B b
Cond x y true  = x
Cond x y false = y

module Xor° = Algebra.CommutativeRing B.commutativeRing-xor-∧
module Bool° = Algebra.CommutativeSemiring B.commutativeSemiring-∧-∨

check : ∀ b → {pf : T b} → ⊤
check = _

If_then_else_ : ∀ {ℓ} {A B : ★ ℓ} b → (T b → A) → (T (not b) → B) → if b then A else B
If_then_else_ true  x _ = x _
If_then_else_ false _ x = x _

If′_then_else_ : ∀ {ℓ} {A B : ★ ℓ} b → A → B → if b then A else B
If′_then_else_ true  x _ = x
If′_then_else_ false _ x = x

If-map : ∀ {A B C D : ★₀} b (f : T b → A → C) (g : T (not b) → B → D) →
           if b then A else B → if b then C else D
If-map true  f _ = f _
If-map false _ f = f _

If-elim : ∀ {A B : ★₀} {P : Bool → ★₀}
            b (f : T b → A → P true) (g : T (not b) → B → P false) → if b then A else B → P b
If-elim true  f _ = f _
If-elim false _ f = f _

If-true : ∀ {A B : ★₀} {b} → T b → (if b then A else B) ≡ A
If-true {b = true}  _ = ≡.refl
If-true {b = false} ()

If-false : ∀ {A B : ★₀} {b} → T (not b) → (if b then A else B) ≡ B
If-false {b = true}  ()
If-false {b = false} _ = ≡.refl

cong-if : ∀ {A B : ★₀} b {t₀ t₁} (f : A → B) → (if b then f t₀ else f t₁) ≡ f (if b then t₀ else t₁)
cong-if true  _ = ≡.refl
cong-if false _ = ≡.refl

if-not : ∀ {a} {A : ★ a} b {t₀ t₁ : A} → (if b then t₀ else t₁) ≡ (if not b then t₁ else t₀)
if-not true  = ≡.refl
if-not false = ≡.refl

data ⟦Bool⟧ : (b₁ b₂ : Bool) → ★₀ where
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

⟦if⟨_⟩_then_else_⟧ : ∀ {a₁ a₂ aᵣ} → (∀⟨ Aᵣ ∶ ⟦★⟧ {a₁} {a₂} aᵣ ⟩⟦→⟧ ⟦Bool⟧ ⟦→⟧ Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ Aᵣ) if_then_else_ if_then_else_
⟦if⟨_⟩_then_else_⟧ _ ⟦true⟧  xᵣ _ = xᵣ
⟦if⟨_⟩_then_else_⟧ _ ⟦false⟧ _ xᵣ = xᵣ

⟦If′⟨_,_⟩_then_else_⟧ : ∀ {ℓ₁ ℓ₂ ℓᵣ} →
                       (∀⟨ Aᵣ ∶ ⟦★⟧ {ℓ₁} {ℓ₂} ℓᵣ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ {ℓ₁} {ℓ₂} ℓᵣ ⟩⟦→⟧
                           ⟨ bᵣ ∶ ⟦Bool⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Bᵣ ⟦→⟧ ⟦if⟨ ⟦★⟧ _ ⟩ bᵣ then Aᵣ else Bᵣ ⟧)
                       If′_then_else_ If′_then_else_
⟦If′⟨_,_⟩_then_else_⟧ _ _ ⟦true⟧  xᵣ _ = xᵣ
⟦If′⟨_,_⟩_then_else_⟧ _ _ ⟦false⟧ _ xᵣ = xᵣ

_==_ : (x y : Bool) → Bool
true == true = true
true == false = false
false == true = false
false == false = true

module == where
  _≈_ : (x y : Bool) → ★₀
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

⟦not⟧ : (⟦Bool⟧ ⟦→⟧ ⟦Bool⟧) not not
⟦not⟧ ⟦true⟧  = ⟦false⟧
⟦not⟧ ⟦false⟧ = ⟦true⟧

_⟦∧⟧_ : (⟦Bool⟧ ⟦→⟧ ⟦Bool⟧ ⟦→⟧ ⟦Bool⟧) _∧_ _∧_
⟦true⟧  ⟦∧⟧ x = x
⟦false⟧ ⟦∧⟧ _ = ⟦false⟧

_⟦∨⟧_ : (⟦Bool⟧ ⟦→⟧ ⟦Bool⟧ ⟦→⟧ ⟦Bool⟧) _∨_ _∨_
⟦true⟧  ⟦∨⟧ _ = ⟦true⟧
⟦false⟧ ⟦∨⟧ x = x

_⟦xor⟧_ : (⟦Bool⟧ ⟦→⟧ ⟦Bool⟧ ⟦→⟧ ⟦Bool⟧) _xor_ _xor_
⟦true⟧  ⟦xor⟧ x = ⟦not⟧ x
⟦false⟧ ⟦xor⟧ x = x

⟦true⟧′ : ∀ {b} → T b → ⟦Bool⟧ true b
⟦true⟧′ {true}  _ = ⟦true⟧
⟦true⟧′ {false} ()

⟦false⟧′ : ∀ {b} → T (not b) → ⟦Bool⟧ false b
⟦false⟧′ {true} ()
⟦false⟧′ {false} _ = ⟦false⟧

≡→T : ∀ {b} → b ≡ true → T b
≡→T ≡.refl = _

≡→Tnot : ∀ {b} → b ≡ false → T (not b)
≡→Tnot ≡.refl = _

T→≡ : ∀ {b} → T b → b ≡ true
T→≡ {true}  _  = ≡.refl
T→≡ {false} ()

Tnot→≡ : ∀ {b} → T (not b) → b ≡ false
Tnot→≡ {false} _  = ≡.refl
Tnot→≡ {true}  ()

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

∧⇒∨ : ∀ x y → T (x ∧ y) → T (x ∨ y)
∧⇒∨ true y = _
∧⇒∨ false y = λ ()

Tdec : ∀ b → Dec (T b)
Tdec true = yes _
Tdec false = no λ()

de-morgan : ∀ x y → not (x ∨ y) ≡ not x ∧ not y
de-morgan true  _ = ≡.refl
de-morgan false _ = ≡.refl

-- false is 0 and true is 1
toℕ : Bool → ℕ
toℕ b = if b then 1 else 0

toℕ≤1 : ∀ b → toℕ b ≤ 1
toℕ≤1 true  = s≤s z≤n
toℕ≤1 false = z≤n

toℕ-⊓ : ∀ a b → toℕ a ⊓ toℕ b ≡ toℕ (a ∧ b)
toℕ-⊓ true true = ≡.refl
toℕ-⊓ true false = ≡.refl
toℕ-⊓ false b = ≡.refl

toℕ-⊔ : ∀ a b → toℕ a ⊔ toℕ b ≡ toℕ (a ∨ b)
toℕ-⊔ true true = ≡.refl
toℕ-⊔ true false = ≡.refl
toℕ-⊔ false b = ≡.refl

toℕ-∸ : ∀ a b → toℕ a ∸ toℕ b ≡ toℕ (a ∧ not b)
toℕ-∸ true true = ≡.refl
toℕ-∸ true false = ≡.refl
toℕ-∸ false true = ≡.refl
toℕ-∸ false false = ≡.refl

xor-not-not : ∀ x y → (not x) xor (not y) ≡ x xor y
xor-not-not true  y = ≡.refl
xor-not-not false y = B.not-involutive y

not-inj : ∀ {x y} → not x ≡ not y → x ≡ y
not-inj {true} {true} _ = ≡.refl
not-inj {true} {false} ()
not-inj {false} {true} ()
not-inj {false} {false} _ = ≡.refl

xor-inj₁ : ∀ x {y z} → x xor y ≡ x xor z → y ≡ z
xor-inj₁ true  = not-inj
xor-inj₁ false = id

xor-inj₂ : ∀ x {y z} → y xor x ≡ z xor x → y ≡ z
xor-inj₂ x {y} {z} rewrite Xor°.+-comm y x | Xor°.+-comm z x = xor-inj₁ x

module Indexed {a} {A : ★ a} where
    _∧°_ : Op₂ (A → Bool)
    x ∧° y = x ⟨ _∧_ ⟩° y

    _∨°_ : Op₂ (A → Bool)
    x ∨° y = x ⟨ _∨_ ⟩° y

    _xor°_ : Op₂ (A → Bool)
    x xor° y = x ⟨ _xor_ ⟩° y

    _==°_ : Op₂ (A → Bool)
    x ==° y = x ⟨ _==_ ⟩° y

    not° : Op₁ (A → Bool)
    not° f = not ∘ f

data So : Bool → ★₀ where
  oh! : So true

So→T : ∀ {b} → So b → T b
So→T oh! = _

T→So : ∀ {b} → T b → So b
T→So {true}  _  = oh!
T→So {false} ()

So→≡ : ∀ {b} → So b → b ≡ true
So→≡ oh! = ≡.refl

≡→So : ∀ {b} → b ≡ true → So b
≡→So ≡.refl = oh!
