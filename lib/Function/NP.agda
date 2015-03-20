{-# OPTIONS --without-K #-}
module Function.NP where

open import Level
  using (_⊔_)
open import Type
  hiding (★)
open import Algebra
  using (module Monoid; Monoid)
open import Algebra.Structures
  using (IsSemigroup)
open import Data.Nat.Base
  using (ℕ; zero; suc)
open import Data.Bool.Base
  renaming (Bool to 𝟚)
open import Data.Product
  using (Σ; _,_)
open import Data.Vec.N-ary
  using (N-ary; N-ary-level)
open import Category.Monad
  using () renaming (module RawMonad to Monad; RawMonad to Monad)
open import Category.Monad.Identity
  using (IdentityMonad)
open import Category.Applicative
  renaming (module RawApplicative to Applicative;
            RawApplicative to Applicative)
open import Relation.Binary
  using (IsEquivalence; module IsEquivalence; _Preserves₂_⟶_⟶_;
         module Setoid)
open import Relation.Binary.PropositionalEquality.NP
  using (_≡_; _≗_; refl; ap; ap₂; module ≡-Reasoning; _→-setoid_; _∙_)
  renaming (isEquivalence to ≡-isEquivalence)

open import Function public

id-app : ∀ {f} → Applicative {f} id
id-app = Monad.rawIApplicative IdentityMonad

-→- : ∀ {a b} (A : ★ a) (B : ★ b) → ★ (a ⊔ b)
-→- A B = A → B

_→⟨_⟩_ : ∀ {a b} (A : ★ a) (n : ℕ) (B : ★ b) → ★ (N-ary-level a b n)
A →⟨ n ⟩ B = N-ary n A B

_→⟨_⟩₀_ : ∀ (A : ★₀) (n : ℕ) (B : ★₀) → ★₀
A →⟨ zero  ⟩₀ B = B
A →⟨ suc n ⟩₀ B = A → A →⟨ n ⟩₀ B

_→⟨_⟩₁_ : ∀ (A : ★₀) (n : ℕ) (B : ★₁) → ★₁
A →⟨ zero  ⟩₁ B = B
A →⟨ suc n ⟩₁ B = A → A →⟨ n ⟩₁ B

Endo : ∀ {a} → ★ a → ★ a
Endo A = A → A

Cmp : ∀ {a} → ★ a → ★ a
Cmp A = A → A → 𝟚

Op₁ : ∀ {a} → ★ a → ★ a
Op₁ A = A → A

Op₂ : ∀ {a} → ★ a → ★ a
Op₂ A = A → A → A

-- More properties about nest/fold are in Data.Nat.NP
nest : ∀ {a} {A : ★ a} → ℕ → Endo (Endo A)
-- TMP nest n f x = fold x f n
nest zero    f x = x
nest (suc n) f x = f (nest n f x)

_$⟨_⟩_ : ∀ {a} {A : ★ a} → Endo A → ℕ → Endo A
_$⟨_⟩_ f n = nest n f

-- If you run a version of Agda without the support of instance
-- arguments, simply comment this definition, very little code rely on it.
it : ∀ {a} {A : ★ a} ⦃ x : A ⦄ → A
it ⦃ x ⦄ = x

_⟨_⟩°_ : ∀ {i a b c} {Ix : ★ i} {A : ★ a} {B : A → ★ b} {C : (x : A) → B x → ★ c}
         → (f  : Ix → A)
         → (op : (x : A) (y : B x) → C x y)
         → (g  : (i : Ix) → B (f i))
         → (i : Ix) → C (f i) (g i)
(f ⟨ _∙_ ⟩° g) x = f x ∙ g x

module Combinators where
    S : ∀ {A B C : ★₀} →
          (A → B → C) →
          (A → B) →
          (A → C)
    S = _ˢ_

    K : ∀ {A B : ★₀} → A → B → A
    K = const

    -- B ≗ _∘_
    B : ∀ {A B C : ★₀} → (B → C) → (A → B) → A → C
    B = S (K S) K

    -- C ≗ flip
    C : ∀ {A B C : ★₀} → (A → B → C) → B → A → C
    C = S (S (K (S (K S) K)) S) (K K)

module EndoMonoid-≈ {a ℓ} {A : ★ a}
                    {_≈_ : Endo A → Endo A → ★ ℓ}
                    (isEquivalence : IsEquivalence _≈_)
                    (∘-cong : _∘′_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_)
                   where
  private
    module ≈ = IsEquivalence isEquivalence
    isSemigroup : IsSemigroup _≈_ _∘′_
    isSemigroup = record { isEquivalence = isEquivalence; assoc = λ _ _ _ → ≈.refl; ∙-cong = ∘-cong }

  monoid : Monoid a ℓ
  monoid = record { Carrier = Endo A; _≈_ = _≈_; _∙_ = _∘′_; ε = id
                  ; isMonoid = record { isSemigroup = isSemigroup
                                      ; identity = (λ _ → ≈.refl) , (λ _ → ≈.refl) } }

  open Monoid monoid public

module EndoMonoid-≡ {a} (A : ★ a) = EndoMonoid-≈ {A = A} ≡-isEquivalence (ap₂ _∘′_)

module EndoMonoid-≗ {a} (A : ★ a) = EndoMonoid-≈ (Setoid.isEquivalence (A →-setoid A))
                                                   (λ {f} {g} {h} {i} p q x → p (h x) ∙ ap g (q x))

Π : ∀ {a b} (A : ★ a) → (B : A → ★ b) → ★ _
Π A B = (x : A) → B x

Πⁱ : ∀ {a b} (A : ★ a) → (B : A → ★ b) → ★ _
Πⁱ A B = {x : A} → B x

module FromΠ (Π : ∀ {a b}(A : ★ a)(B : A → ★ b) → ★(a ⊔ b)) where

  module _ {a b}{A : ★ a}(B : A → ★ b) where
    ∀₁ : ★(a ⊔ b)
    ∀₁ = Π A B

  module _ {a b c}{A : ★ a}{B : A → ★ b}(C : (x : A)(y : B x) → ★ c) where
    ∀₂ : ★(a ⊔ b ⊔ c)
    ∀₂ = Π A λ x → Π (B x) (C _)

  module _ {a b c d}{A : ★ a}{B : A → ★ b}{C : {x : A}(y : B x) → ★ c}
           (D : (x : A)(y : B x)(z : C y) → ★ d) where
    ∀₃ : ★(a ⊔ b ⊔ c ⊔ d)
    ∀₃ = Π A λ x → Π (B x) λ y → Π (C y) (D _ _)

  module _ {a b c d e}{A : ★ a}{B : A → ★ b}{C : {x : A}(y : B x) → ★ c}
           {D : {x : A}{y : B x}(z : C y) → ★ d}
           (E : (x : A)(y : B x)(z : C y)(t : D z) → ★ e)
           where
    ∀₄ : ★(a ⊔ b ⊔ c ⊔ d ⊔ e)
    ∀₄ = Π A λ x → Π (B x) λ y → Π (C y) λ z → Π (D z) (E _ _ _)

module FromΣ (Σ : ∀ {a b}(A : ★ a)(B : A → ★ b) → ★(a ⊔ b)) =
  FromΠ Σ renaming (∀₁ to ∃₁; ∀₂ to ∃₂; ∀₃ to ∃₃; ∀₄ to ∃₄)

module FromΠΣ (Π Σ : ∀ {a b}(A : ★ a)(B : A → ★ b) → ★(a ⊔ b))
              (_,_ : ∀ {a b}{A : ★ a}{B : A → ★ b}(x : A)(y : B x) → Σ A B) where
  module _ {a b c}(A : ★ a)(B : A → ★ b)(C : Σ A B → ★ c) where
    ΠΠ ΠΣ ΣΠ : ★ _
    ΠΠ = Π A λ x → Π (B x) λ y → C (x , y)
    ΠΣ = Π A λ x → Σ (B x) λ y → C (x , y)
    ΣΠ = Σ A λ x → Π (B x) λ y → C (x , y)
    ΣΣ = Σ A λ x → Σ (B x) λ y → C (x , y)

  module _ {a b c d}(A : ★ a)(B : A → ★ b)(C : Σ A B → ★ c)
           (D : Σ (Σ A B) C → ★ d) where
    ΠΠΠ ΠΣΠ ΠΣΣ ΣΠΣ ΣΠΠ : ★ _
    ΠΠΠ = Π A λ x → Π (B x) λ y → Π (C (x , y)) λ z → D ((x , y) , z)
    ΠΣΠ = Π A λ x → Σ (B x) λ y → Π (C (x , y)) λ z → D ((x , y) , z)
    ΠΣΣ = Π A λ x → Σ (B x) λ y → Σ (C (x , y)) λ z → D ((x , y) , z)
    ΣΠΣ = Σ A λ x → Π (B x) λ y → Σ (C (x , y)) λ z → D ((x , y) , z)
    ΣΠΠ = Σ A λ x → Π (B x) λ y → Π (C (x , y)) λ z → D ((x , y) , z)

module Implicits where
  open FromΠ  Πⁱ       public
  open FromΠΣ Πⁱ Σ _,_ public

module Explicits where
  open FromΠ  Π       public
  open FromΣ  Σ       public
  open FromΠΣ Π Σ _,_ public
-- -}
