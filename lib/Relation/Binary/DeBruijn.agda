{-# OPTIONS --universe-polymorphism #-}
module Relation.Binary.DeBruijn where

import Level as L
open L using (Lift; lift)
open import Data.Nat.NP hiding (_⊔_)
open import Data.Product.NP
open import Data.Unit hiding (_≤?_)
open import Data.Sum.NP
open import Data.List
open import Data.Bool
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.Simple
open import Relation.Binary.Permutation
open import Relation.Binary.Bijection
open import Relation.Binary.Sum.NP
import Relation.Binary.On.NP as On
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_;_≢_)
open ≡.≡-Reasoning
import Data.Nat.Properties as Nat

-- show that List Bool ≅ ℘(ℕ) ≅ ø (+1|^1) ≅ ø (+k|^k)★

private
  infix 2 _⇔_
  _⇔_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} (R₁ : REL A B ℓ₁) (R₂ : REL A B ℓ₂) → Set _
  R₁ ⇔ R₂ = R₁ ⇒ R₂ × R₂ ⇒ R₁

  Ext≡→⇔ : ∀ {ℓ a b} {A : Set a} {B : Set b} {_∼₁_ _∼₂_ : REL A B ℓ}
             (ext : ∀ {i j} → i ∼₁ j ≡ i ∼₂ j)
           → _∼₁_ ⇔ _∼₂_
  Ext≡→⇔ f = (λ x → ≡.subst id f x) , λ x → ≡.subst id (≡.sym f) x

module Data where
  data _^¹ {a} (α : Rel ℕ a) : Rel ℕ a where
    zero : (α ^¹) 0 0
    suc  : ∀ {i j}
           (αij :     α i j              )
           →      ----------------------
                  (α ^¹) (suc i) (suc j)

  -- Iterated version of _^¹
  data _^_ {a} (α : Rel ℕ a) : ℕ → Rel ℕ a where
    zero : ∀ {i j}
           (αij :    α i j   )
           →      -----------
                  (α ^ 0) i j
    suc  : ∀ {i j n}
           (αⁿ¹ij : ((α ^¹) ^ n) i j )
           →        ----------------
                    (α ^ suc n) i j

data IdFin : ℕ → Rel ℕ L.zero where
  zero : ∀ {n} → IdFin (suc n) 0 0
  suc  : ∀ {n i j} → IdFin n i j → IdFin (suc n) (suc i) (suc j)

_+ᵢ_ : ∀ {a} → Rel ℕ a → ℕ → Rel ℕ a
_+ᵢ_ _∼_ n i j = (i + n) ∼ (j + n)
infixl 6 _+ᵢ_

_+ᵢ'_ : ∀ {a} → Rel ℕ a → ℕ → Rel ℕ a
_+ᵢ'_ _∼_ n i j = (n + i) ∼ (n + j)
infixl 6 _+ᵢ'_

dispatch-≤ : ∀ (k x : ℕ) → ℕ ⊎ ℕ
dispatch-≤ k x = if ⌊ x ≤? k ⌋ then inj₁ x else inj₂ x

dispatch-< : ∀ (k x : ℕ) → ℕ ⊎ ℕ
dispatch-< = dispatch-≤ ∘ suc

Import : ∀ {a} (k₁ k₂ : ℕ) → Rel ℕ a → Rel ℕ a
Import k₁ k₂ α = (_≡_ ⊎-Rel (α +ᵢ k₂)) on (dispatch-< k₁)
-- Import k₁ k₂ α = (IdFin k₁ ⊎-Rel (α +ᵢ k₂)) on (dispatch-< k₁)

module IdFin-Props where
  idFin-≡ : ∀ {k x y} → IdFin k x y → x ≡ y
  idFin-≡ zero = ≡.refl
  idFin-≡ (suc x) rewrite idFin-≡ x = ≡.refl

module +ᵢ-Props where
  +ᵢ-pres-bij : ∀ {a k} {α : Rel ℕ a} → BijectiveREL ℕ ℕ α → BijectiveREL ℕ ℕ (α +ᵢ k)
  +ᵢ-pres-bij {a} {k} = On.bijective (λ x → x + k) (cancel-+-right k)
     where
       cancel-+-right : ∀ {i j} k → i + k ≡ j + k → i ≡ j
       cancel-+-right {i} {j} k eq₁
         = Nat.cancel-+-left k
            (k + i ≡⟨ ℕ°.+-comm k i ⟩ i + k ≡⟨ eq₁ ⟩ j + k ≡⟨ ℕ°.+-comm j k ⟩ k + j ∎)

  +ᵢ-0-id : ∀ {a} (α : Rel _ a) {i j} → (α +ᵢ 0) i j ≡ α i j
  +ᵢ-0-id α {i} {j} rewrite ℕ°.+-comm i 0 | ℕ°.+-comm j 0 = ≡.refl

  +ᵢ-0-id' : ∀ {a} (α : Rel _ a) → (α +ᵢ 0) ⇔ α
  +ᵢ-0-id' = Ext≡→⇔ ∘ +ᵢ-0-id

module ImportProps where
  Import-pres-bij : ∀ {a k₁ k₂} {α : Rel ℕ a} → BijectiveREL ℕ ℕ α → BijectiveREL ℕ ℕ (Import k₁ k₂ α)
  Import-pres-bij {k₁ = k₁} α-bij
    = On.bijective (dispatch-< k₁) dispatch-<-k₁-inj
        (≡.bijective ⊎-preserve-bijections (+ᵢ-pres-bij α-bij))
     where
       open +ᵢ-Props
       dispatch-<-k₁-inj : ∀ {i j} → dispatch-< k₁ i ≡ dispatch-< k₁ j → i ≡ j
       dispatch-<-k₁-inj {i} {j} with i ≤? suc k₁ | j ≤? suc k₁
       ... | yes _ | yes _ = inj₁-inj
       ... | no _  | no _  = inj₂-inj
       ... | yes _ | no _  = λ()
       ... | no _  | yes _ = λ()

  -- Import 0 k₂ α

{-
Bijℕ : Set
Bijℕ = ∃[ n ](Vec (Maybe (Fin n)) n)

Bijℕ : Set
Bijℕ = List (Maybe ℕ)
-}

open Data public using (_^¹)

module Fun where
  _^_ : ∀ {a} (α : Rel ℕ a) → ℕ → Rel ℕ a
  α ^ zero = α
  α ^ suc n = (α ^¹) ^ n

  _^'_ : ∀ {a} (α : Rel ℕ a) → ℕ → Rel ℕ a
  α ^' zero = α
  α ^' suc n = (α ^' n) ^¹

module Fun-Data-^-equiv where
  open Fun
  open Data renaming (_^_ to _^d_)
  ⟹ : ∀ {a} {α : Rel ℕ a} n → α ^ n ⇒ α ^d n
  ⟹ zero     = zero
  ⟹ (suc n)  = suc ∘′ ⟹ n
  ⇐ : ∀ {a} {α : Rel ℕ a} n → α ^d n ⇒ α ^ n
  ⇐ zero    (zero x)  = x
  ⇐ (suc n) (suc x)   = ⇐ n x

open Fun public

module Props where
  ^-assoc : ∀ {a} (α : Rel ℕ a) m n → (α ^ m) ^ n ≡ α ^ (m + n)
  ^-assoc α zero n                                = ≡.refl
  ^-assoc α (suc m) n rewrite ^-assoc (α ^¹) m n  = ≡.refl

  ^-comm : ∀ {a} (α : Rel ℕ a) m n → (α ^ m) ^ n ≡ (α ^ n) ^ m
  ^-comm α m n rewrite ^-assoc α n m
                     | ℕ°.+-comm n m
                     | ≡.sym (^-assoc α m n)
                     = ≡.refl

  ^¹-comm-^ : ∀ {a} (α : Rel ℕ a) n → (α ^¹) ^ n ≡ (α ^ n) ^¹
  ^¹-comm-^ α n = ^-comm α 1 n

module Fun-^-equiv-^' where
  open Props
  open Fun
  open Data hiding (_^_)

  ^¹-pres-⇒ : ∀ {a b} {α : Rel ℕ a} {β : Rel ℕ b} → α ⇒ β → (α ^¹) ⇒ (β ^¹)
  ^¹-pres-⇒ f zero = zero
  ^¹-pres-⇒ f (suc x) = suc (f x)

  ⟹ : ∀ {a} (α : Rel ℕ a) n → α ^ n ⇒ α ^' n
  ⟹ _ zero     x = x
  ⟹ α (suc n) {i} {j} x = ^¹-pres-⇒ (⟹ α n) ((≡.subst (λ x → x i j) (^¹-comm-^ α n)) x)

  ⇐ : ∀ {a} (α : Rel ℕ a) n → α ^' n ⇒ α ^ n
  ⇐ _ zero    x = x
  ⇐ α (suc n) {i} {j} x = ≡.subst (λ x → x i j) (≡.sym (^¹-comm-^ α n)) (^¹-pres-⇒ (⇐ α n) x)

open Fun public

module IdFin⇔Never^ where
  open Data hiding (_^_)
  open Props

  ⟹' : ∀ n → IdFin n ⇒ Never ^' n
  ⟹' zero ()
  ⟹' (suc n) zero = zero
  ⟹' (suc n) (suc x) = suc (⟹' n x)

  ⟹ : ∀ {n} → IdFin n ⇒ Never ^ n
  ⟹ {n} = Fun-^-equiv-^'.⇐ Never n ∘ ⟹' n

  ⇐' : ∀ n → Never ^' n ⇒ IdFin n
  ⇐' zero    (lift ())
  ⇐' (suc n) zero      = zero
  ⇐' (suc n) (suc αij) = suc (⇐' n αij)

  ⇐ : ∀ {n} → Never ^ n ⇒ IdFin n
  ⇐ {n} = ⇐' n ∘ Fun-^-equiv-^'.⟹ Never n
