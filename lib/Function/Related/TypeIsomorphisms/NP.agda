module Function.Related.TypeIsomorphisms.NP where

import Level as L
open import Algebra
import Algebra.FunctionProperties as FP
open L using (Lift; lower; lift)
open import Type

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_) renaming (_^_ to _**_)
open import Data.Maybe.NP
open import Data.Product renaming (map to map×)
--open import Data.Product.N-ary
open import Data.Sum renaming (map to map⊎)
open import Data.Unit
open import Data.Empty

import Function as F
import Function.Equality as FE
open FE using (_⟨$⟩_)
open import Function.Related as FR
open import Function.Related.TypeIsomorphisms public
import Function.Inverse as Inv
open Inv using (_↔_; _∘_; sym; id; module Inverse)
open import Relation.Binary
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.Sum
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (→-to-⟶)


Inv-isEquivalence : IsEquivalence (Inv.Inverse {f₁ = L.zero} {f₂ = L.zero})
Inv-isEquivalence = record
   { refl = Inv.id
   ; sym = Inv.sym
   ; trans = F.flip Inv._∘_ }

SEToid : Set _
SEToid = Setoid L.zero L.zero

SEToid₁ : Setoid _ _
SEToid₁ = record
  { Carrier = Setoid L.zero L.zero
  ; _≈_ = Inv.Inverse
  ; isEquivalence = Inv-isEquivalence }

⊎-ICommutativeMonoid : CommutativeMonoid _ _
⊎-ICommutativeMonoid = record {
                         Carrier = SEToid ;
                         _≈_ = Inv.Inverse;
                         _∙_ = _⊎-setoid_;
                         ε = ≡.setoid ⊥;
                         isCommutativeMonoid = record
                            { isSemigroup = record
                              { isEquivalence = Inv-isEquivalence
                              ; assoc = assoc
                              ; ∙-cong = _⊎-inverse_
                              }
                            ; identityˡ = left-identity
                            ; comm = comm
                            }
                         }
  where
  open FP (Inv.Inverse {f₁ = L.zero}{f₂ = L.zero})

  left-identity : LeftIdentity (≡.setoid ⊥) _⊎-setoid_
  left-identity A = record
    { to = record
      { _⟨$⟩_ = [ (λ ()) , F.id ]
      ; cong  = cong-to
      }
    ; from = record
      { _⟨$⟩_ = inj₂
      ; cong = ₂∼₂
      }
    ; inverse-of = record
      { left-inverse-of = [ (λ ()) , (λ x → ₂∼₂ refl) ]
      ; right-inverse-of = λ x → refl
      }
    } where open Setoid A
            cong-to : Setoid._≈_ (≡.setoid ⊥ ⊎-setoid A) =[ _ ]⇒ _≈_
            cong-to (₁∼₂ ())
            cong-to (₁∼₁ x∼₁y) rewrite x∼₁y = refl
            cong-to (₂∼₂ x∼₂y) = x∼₂y

  assoc : Associative _⊎-setoid_
  assoc A B C = record
    { to = record
      { _⟨$⟩_ = [ [ inj₁ , inj₂ F.∘ inj₁ ] , inj₂ F.∘ inj₂ ]
      ; cong = cong-to
      }
    ; from = record
      { _⟨$⟩_ = [ inj₁ F.∘ inj₁ , [ inj₁ F.∘ inj₂ , inj₂ ] ]
      ; cong = cong-from
      }
    ; inverse-of = record
      { left-inverse-of = [ [ (λ _ → ₁∼₁ (₁∼₁ (refl A))) , (λ _ → ₁∼₁ (₂∼₂ (refl B)) ) ] , (λ _ → ₂∼₂ (refl C)) ]
      ; right-inverse-of = [ (λ _ → ₁∼₁ (refl A)) , [ (λ _ → ₂∼₂ (₁∼₁ (refl B))) , (λ _ → ₂∼₂ (₂∼₂ (refl C))) ] ]
      }
    } where
      open Setoid
      cong-to : _≈_ ((A ⊎-setoid B) ⊎-setoid C) =[ _ ]⇒ _≈_ (A ⊎-setoid (B ⊎-setoid C))
      cong-to (₁∼₂ ())
      cong-to (₁∼₁ (₁∼₂ ()))
      cong-to (₁∼₁ (₁∼₁ x∼₁y)) = ₁∼₁ x∼₁y
      cong-to (₁∼₁ (₂∼₂ x∼₂y)) = ₂∼₂ (₁∼₁ x∼₂y)
      cong-to (₂∼₂ x∼₂y) = ₂∼₂ (₂∼₂ x∼₂y)

      cong-from : _≈_ (A ⊎-setoid (B ⊎-setoid C)) =[ _ ]⇒ _≈_ ((A ⊎-setoid B) ⊎-setoid C)
      cong-from (₁∼₂ ())
      cong-from (₁∼₁ x∼₁y) = ₁∼₁ (₁∼₁ x∼₁y)
      cong-from (₂∼₂ (₁∼₂ ()))
      cong-from (₂∼₂ (₁∼₁ x∼₁y)) = ₁∼₁ (₂∼₂ x∼₁y)
      cong-from (₂∼₂ (₂∼₂ x∼₂y)) = ₂∼₂ x∼₂y

  comm : Commutative _⊎-setoid_
  comm A B = record
    { to = swap'
    ; from = swap'
    ; inverse-of = record
      { left-inverse-of  = inv A B
      ; right-inverse-of = inv B A
      }
    } where
      swap' : ∀ {A B : SEToid} → A ⊎-setoid B FE.⟶ B ⊎-setoid A
      swap' {A} {B} = record
        { _⟨$⟩_ = [ inj₂ , inj₁ ]
        ; cong = cong
        } where
          cong : Setoid._≈_ (A ⊎-setoid B) =[ _ ]⇒ Setoid._≈_ (B ⊎-setoid A)
          cong (₁∼₂ ())
          cong (₁∼₁ x∼₁y) = ₂∼₂ x∼₁y
          cong (₂∼₂ x∼₂y) = ₁∼₁ x∼₂y

      inv : ∀ A B → ∀ x → Setoid._≈_ (A ⊎-setoid B) (swap' FE.∘ swap' {A} {B}⟨$⟩ x) x
      inv A B = [ (λ _ → ₁∼₁ (Setoid.refl A)) , (λ _ → ₂∼₂ (Setoid.refl B)) ]

×-ICommutativeMonoid : CommutativeMonoid _ _
×-ICommutativeMonoid = record {
                         Carrier = SEToid ;
                         _≈_ = Inv.Inverse;
                         _∙_ = _×-setoid_;
                         ε = ≡.setoid ⊤;
                         isCommutativeMonoid = record
                            { isSemigroup = record
                              { isEquivalence = Inv-isEquivalence
                              ; assoc = assoc
                              ; ∙-cong = _×-inverse_
                              }
                            ; identityˡ = left-identity
                            ; comm = comm
                            }
                         }
  where
  open FP (Inv.Inverse {f₁ = L.zero}{f₂ = L.zero})

  left-identity : LeftIdentity (≡.setoid ⊤) _×-setoid_
  left-identity A = record
    { to = record
      { _⟨$⟩_ = proj₂
      ; cong = proj₂
      }
    ; from = record
      { _⟨$⟩_ = λ x → _ , x
      ; cong = λ x → ≡.refl , x
      }
    ; inverse-of = record
      { left-inverse-of = λ x → ≡.refl , (Setoid.refl A)
      ; right-inverse-of = λ x → Setoid.refl A
      }
    }

  assoc : Associative _×-setoid_
  assoc A B C = record
    { to = record
      { _⟨$⟩_ = < proj₁ F.∘ proj₁ , < proj₂ F.∘ proj₁ , proj₂ > >
      ; cong  = < proj₁ F.∘ proj₁ , < proj₂ F.∘ proj₁ , proj₂ > >
      }
    ; from = record
      { _⟨$⟩_ = < < proj₁ , proj₁ F.∘ proj₂ > , proj₂ F.∘ proj₂ >
      ; cong  = < < proj₁ , proj₁ F.∘ proj₂ > , proj₂ F.∘ proj₂ >
      }
    ; inverse-of = record
      { left-inverse-of = λ _ → Setoid.refl ((A ×-setoid B) ×-setoid C)
      ; right-inverse-of = λ _ → Setoid.refl (A ×-setoid (B ×-setoid C))
      }
    }

  comm : Commutative _×-setoid_
  comm A B = record
    { to = swap' {A} {B}
    ; from = swap' {B} {A}
    ; inverse-of = record
      { left-inverse-of = inv A B
      ; right-inverse-of = inv B A
      }
    } where
      swap' : ∀ {A B : SEToid} → A ×-setoid B FE.⟶ B ×-setoid A
      swap' {A}{B} = record { _⟨$⟩_ = swap; cong = swap }

      inv : ∀ A B → ∀ x → Setoid._≈_ (A ×-setoid B) (swap' {B} {A} FE.∘ swap' {A} {B}⟨$⟩ x) x
      inv A B = λ x → Setoid.refl (A ×-setoid B)

×⊎-ICommutativeSemiring : CommutativeSemiring _ _
×⊎-ICommutativeSemiring = record
  { Carrier = SEToid
  ; _≈_ = Inv.Inverse
  ; _+_ = _⊎-setoid_
  ; _*_ = _×-setoid_
  ; 0# = ≡.setoid ⊥
  ; 1# = ≡.setoid ⊤
  ; isCommutativeSemiring = record
    { +-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid ⊎-ICommutativeMonoid
    ; *-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid ×-ICommutativeMonoid
    ; distribʳ = distribʳ
    ; zeroˡ = zeroˡ
    }
  }
  where
  open FP (Inv.Inverse {f₁ = L.zero}{f₂ = L.zero})

  distribʳ : _×-setoid_ DistributesOverʳ _⊎-setoid_
  distribʳ A B C = record
    { to = record
      { _⟨$⟩_ = uncurry [ curry inj₁ , curry inj₂ ]
      ; cong = cong-to
      }
    ; from = record
      { _⟨$⟩_ = from
      ; cong = cong-from
      }
    ; inverse-of = record
      { left-inverse-of  = uncurry [ (λ x y → (₁∼₁ (refl B)) , (refl A)) , (λ x y → (₂∼₂ (refl C)) , (refl A)) ]
      ; right-inverse-of = [ uncurry (λ x y → ₁∼₁ ((refl B {x}) , (refl A {y})))
                           , uncurry (λ x y → ₂∼₂ ((refl C {x}) , (refl A {y}))) ]
      }
    } where
      open Setoid
      A' = Carrier A
      B' = Carrier B
      C' = Carrier C

      cong-to : _≈_ ((B ⊎-setoid C) ×-setoid A) =[ _ ]⇒ _≈_ ((B ×-setoid A) ⊎-setoid (C ×-setoid A))
      cong-to (₁∼₂ () , _)
      cong-to (₁∼₁ x∼₁y , A-rel) = ₁∼₁ (x∼₁y , A-rel)
      cong-to (₂∼₂ x∼₂y , A-rel) = ₂∼₂ (x∼₂y , A-rel)

      from : B' × A' ⊎ C' × A' → (B' ⊎ C') × A'
      from = [ map× inj₁ F.id , map× inj₂ F.id ]

      cong-from : _≈_ ((B ×-setoid A) ⊎-setoid (C ×-setoid A)) =[ _ ]⇒ _≈_ ((B ⊎-setoid C) ×-setoid A)
      cong-from (₁∼₂ ())
      cong-from (₁∼₁ (B-rel , A-rel)) = (₁∼₁ B-rel , A-rel)
      cong-from (₂∼₂ (C-rel , A-rel)) = ₂∼₂ C-rel , A-rel

  zeroˡ : LeftZero (≡.setoid ⊥) _×-setoid_
  zeroˡ A = record
    { to = record
      { _⟨$⟩_ = proj₁
      ; cong = proj₁
      }
    ; from = record
      { _⟨$⟩_ = ⊥-elim
      ; cong = λ { {()} x }
      }
    ; inverse-of = record
      { left-inverse-of = λ x → ⊥-elim (proj₁ x)
      ; right-inverse-of = λ x → ⊥-elim x
      }
    }

module ×-CMon = CommutativeMonoid (×-CommutativeMonoid FR.bijection L.zero)
module ⊎-CMon = CommutativeMonoid (⊎-CommutativeMonoid FR.bijection L.zero)
module ×⊎°    = CommutativeSemiring (×⊎-CommutativeSemiring FR.bijection L.zero)

module ×-ICMon = CommutativeMonoid ×-ICommutativeMonoid
module ⊎-ICMon = CommutativeMonoid ⊎-ICommutativeMonoid
module ×⊎°I    = CommutativeSemiring ×⊎-ICommutativeSemiring

swap-iso : ∀ {A B} → (A × B) ↔ (B × A)
swap-iso = ×-CMon.comm _ _

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

⊤×A↔A : ∀ {A : ★} → (⊤ × A) ↔ A
⊤×A↔A = proj₁ ×-CMon.identity _ ∘ sym Lift↔id ×-cong id

A×⊤↔A : ∀ {A : ★} → (A × ⊤) ↔ A
A×⊤↔A = proj₂ ×-CMon.identity _ ∘ id ×-cong sym Lift↔id

⊥⊎A↔A : ∀ {A : ★} → (⊥ ⊎ A) ↔ A
⊥⊎A↔A = proj₁ ⊎-CMon.identity _ ∘ sym Lift↔id ⊎-cong id

A⊎⊥↔A : ∀ {A : ★} → (A ⊎ ⊥) ↔ A
A⊎⊥↔A = proj₂ ⊎-CMon.identity _ ∘ id ⊎-cong sym Lift↔id

⊥×A↔⊥ : ∀ {A : ★} → (⊥ × A) ↔ ⊥
⊥×A↔⊥ = Lift↔id ∘ proj₁ ×⊎°.zero _ ∘ sym (Lift↔id ×-cong id)

Maybe⊥↔⊤ : Maybe ⊥ ↔ ⊤
Maybe⊥↔⊤ = A⊎⊥↔A ∘ Maybe↔⊤⊎

Maybe^⊥↔Fin : ∀ n → Maybe^ n ⊥ ↔ Fin n
Maybe^⊥↔Fin zero    = sym Fin0↔⊥
Maybe^⊥↔Fin (suc n) = sym Fin∘suc↔Maybe∘Fin ∘ Maybe-cong (Maybe^⊥↔Fin n)

Maybe^⊤↔Fin1+ : ∀ n → Maybe^ n ⊤ ↔ Fin (suc n)
Maybe^⊤↔Fin1+ n = Maybe^⊥↔Fin (suc n) ∘ sym (Maybe∘Maybe^↔Maybe^∘Maybe n) ∘ Maybe^-cong n (sym Maybe⊥↔⊤)

Maybe-⊎ : ∀ {A B : ★} → (Maybe A ⊎ B) ↔ Maybe (A ⊎ B)
Maybe-⊎ = sym Maybe↔⊤⊎ ∘ ⊎-CMon.assoc ⊤ _ _ ∘ (Maybe↔⊤⊎ ⊎-cong id)

Maybe^-⊎-+ : ∀ {A} m n → (Maybe^ m ⊥ ⊎ Maybe^ n A) ↔ Maybe^ (m + n) A
Maybe^-⊎-+ zero    n = ⊥⊎A↔A
Maybe^-⊎-+ (suc m) n = Maybe-cong (Maybe^-⊎-+ m n) ∘ Maybe-⊎

Fin-⊎-+ : ∀ m n → (Fin m ⊎ Fin n) ↔ Fin (m + n)
Fin-⊎-+ m n = Maybe^⊥↔Fin (m + n)
            ∘ Maybe^-⊎-+ m n
            ∘ sym (Maybe^⊥↔Fin m ⊎-cong Maybe^⊥↔Fin n)

Fin∘suc↔⊤⊎Fin : ∀ {n} → Fin (suc n) ↔ (⊤ ⊎ Fin n)
Fin∘suc↔⊤⊎Fin = Maybe↔⊤⊎ ∘ Fin∘suc↔Maybe∘Fin
