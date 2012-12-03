module Function.Related.TypeIsomorphisms.NP where

import Level as L
open import Algebra
open L using (Lift; lower; lift)
open import Type
import Function as F
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe.NP
open import Data.Product
--open import Data.Product.N-ary
open import Data.Sum renaming (map to map⊎)
open import Data.Unit
open import Data.Empty
open import Function.Equality using (_⟨$⟩_)
open import Function.Related
open import Function.Related.TypeIsomorphisms public
open import Function.Inverse using (_↔_; _∘_; sym; id; module Inverse)
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.Sum
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (→-to-⟶)

Maybe↔⊤⊎ : ∀ {a} {A : Set a} → Maybe A ↔ (⊤ ⊎ A)
Maybe↔⊤⊎
  = record { to   = →-to-⟶ (maybe inj₂ (inj₁ _))
           ; from = →-to-⟶ [ F.const nothing , just ]
           ; inverse-of
           = record { left-inverse-of = maybe (λ _ → ≡.refl) ≡.refl
                    ; right-inverse-of = [ (λ _ → ≡.refl) , (λ _ → ≡.refl) ] } }

Maybe-cong : ∀ {a b} {A : Set a} {B : Set b} → A ↔ B → Maybe A ↔ Maybe B 
Maybe-cong A↔B = sym Maybe↔⊤⊎ ∘ id ⊎-cong A↔B ∘ Maybe↔⊤⊎

Maybe∘Maybe^↔Maybe^∘Maybe : ∀ {A} n → Maybe (Maybe^ n A) ↔ Maybe^ n (Maybe A)
Maybe∘Maybe^↔Maybe^∘Maybe zero    = id
Maybe∘Maybe^↔Maybe^∘Maybe (suc n) = Maybe-cong (Maybe∘Maybe^↔Maybe^∘Maybe n)

Maybe^-cong : ∀ {A B} n → A ↔ B → Maybe^ n A ↔ Maybe^ n B
Maybe^-cong zero    = F.id
Maybe^-cong (suc n) = Maybe-cong F.∘ Maybe^-cong n

Vec0↔⊤ : ∀ {a} {A : Set a} → Vec A 0 ↔ ⊤
Vec0↔⊤ = record { to         = →-to-⟶ _
                ; from       = →-to-⟶ (F.const [])
                ; inverse-of = record { left-inverse-of  = λ { [] → ≡.refl }
                                      ; right-inverse-of = λ _ → ≡.refl } }

Vec∘suc↔A×Vec : ∀ {a} {A : Set a} {n} → Vec A (suc n) ↔ (A × Vec A n)
Vec∘suc↔A×Vec
  = record { to         = →-to-⟶ (λ { (x ∷ xs) → x , xs })
           ; from       = →-to-⟶ (uncurry _∷_)
           ; inverse-of = record { left-inverse-of  = λ { (x ∷ xs) → ≡.refl }
                                 ; right-inverse-of = λ _ → ≡.refl } }

infix 8 _^_

_^_ : ★ → ℕ → ★
A ^ 0     = ⊤
A ^ suc n = A × A ^ n

^↔Vec : ∀ {A} n → (A ^ n) ↔ Vec A n
^↔Vec zero    = sym Vec0↔⊤
^↔Vec (suc n) = sym Vec∘suc↔A×Vec ∘ (id ×-cong (^↔Vec n))

Fin0↔⊥ : Fin 0 ↔ ⊥
Fin0↔⊥ = record { to   = →-to-⟶ λ()
                ; from = →-to-⟶ λ()
                ; inverse-of = record { left-inverse-of  = λ()
                                      ; right-inverse-of = λ() } }

Fin∘suc↔Maybe∘Fin : ∀ {n} → Fin (suc n) ↔ Maybe (Fin n)
Fin∘suc↔Maybe∘Fin {n}
  = record { to   = →-to-⟶ to
           ; from = →-to-⟶ (maybe suc zero)
           ; inverse-of
           = record { left-inverse-of = λ { zero → ≡.refl ; (suc n) → ≡.refl }
                    ; right-inverse-of = maybe (λ _ → ≡.refl) ≡.refl } }
  where to : Fin (suc n) → Maybe (Fin n)
        to zero = nothing
        to (suc n) = just n

Lift↔id : ∀ {a} {A : Set a} → Lift {a} {a} A ↔ A
Lift↔id = record { to = →-to-⟶ lower
                 ; from = →-to-⟶ lift
                 ; inverse-of = record { left-inverse-of = λ { (lift x) → ≡.refl }
                                       ; right-inverse-of = λ _ → ≡.refl } }

Maybe⊥↔⊤ : Maybe ⊥ ↔ ⊤
Maybe⊥↔⊤ = (proj₂ CMon.identity ⊤ ∘ id ⊎-cong (sym (Lift↔id {A = ⊥}))) ∘ Maybe↔⊤⊎
  where module CMon = CommutativeMonoid (⊎-CommutativeMonoid bijection L.zero)

Maybe^⊥↔Fin : ∀ n → Maybe^ n ⊥ ↔ Fin n
Maybe^⊥↔Fin zero    = sym Fin0↔⊥
Maybe^⊥↔Fin (suc n) = sym Fin∘suc↔Maybe∘Fin ∘ Maybe-cong (Maybe^⊥↔Fin n)

Maybe^⊤↔Fin1+ : ∀ n → Maybe^ n ⊤ ↔ Fin (suc n)
Maybe^⊤↔Fin1+ n = Maybe^⊥↔Fin (suc n) ∘ sym (Maybe∘Maybe^↔Maybe^∘Maybe n) ∘ Maybe^-cong n (sym Maybe⊥↔⊤)

Fin∘suc↔⊤⊎Fin : ∀ {n} → Fin (suc n) ↔ (⊤ ⊎ Fin n)
Fin∘suc↔⊤⊎Fin = Maybe↔⊤⊎ ∘ Fin∘suc↔Maybe∘Fin
