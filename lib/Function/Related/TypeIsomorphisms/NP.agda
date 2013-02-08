module Function.Related.TypeIsomorphisms.NP where

import Level as L
open import Algebra
import Algebra.FunctionProperties as FP
open L using (Lift; lower; lift)
open import Type hiding (★)

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
import Function.Inverse.NP as Inv
open Inv using (_↔_; _∘_; sym; id; inverses; module Inverse)
open import Relation.Binary
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.Sum
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_ ; _≢_)

module CancelMaybe where
  private
    module _ {A : Set} where
      just-inj : {x y : A} → Maybe.just x ≡ just y → x ≡ y
      just-inj ≡.refl = ≡.refl

    module _ {A B : Set}
      (f : Maybe A ↔ Maybe B)
      (tof-tot : ∀ x → Inverse.to f ⟨$⟩ just x ≢ nothing)
      (fof-tot : ∀ x → Inverse.from f ⟨$⟩ just x ≢ nothing) where

        CancelMaybe' : A ↔ B
        CancelMaybe' = inverses (⇒) (⇐) ⇐⇒ ⇒⇐ where
          to = λ x → Inverse.to f ⟨$⟩ x
          from = λ x → Inverse.from f ⟨$⟩ x

          ⇒ : _ → _
          ⇒ x with to (just x) | tof-tot x
          ⇒ x | just x₁ | _ = x₁
          ⇒ x | nothing | p = ⊥-elim (p ≡.refl)

          ⇐ : _ → _
          ⇐ x with from (just x) | fof-tot x
          ⇐ x | just x₁ | p = x₁
          ⇐ x | nothing | p = ⊥-elim (p ≡.refl)

          ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
          ⇐⇒ x with to (just x)
                  | tof-tot x
                  | from (just (⇒ x))
                  | fof-tot (⇒ x)
                  | Inverse.left-inverse-of f (just x)
                  | Inverse.right-inverse-of f (just (⇒ x))
          ⇐⇒ x | just x₁ | p | just x₂ | q | b | c  = just-inj (≡.trans (≡.sym (Inverse.left-inverse-of f (just x₂))) (≡.trans (≡.cong from c) b))
          ⇐⇒ x | just x₁ | p | nothing | q | _ | _  = ⊥-elim (q ≡.refl)
          ⇐⇒ x | nothing | p | z       | q | _ | _  = ⊥-elim (p ≡.refl)

          ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
          ⇒⇐ x with from (just x)
                  | fof-tot x
                  | to (just (⇐ x))
                  | tof-tot (⇐ x)
                  | Inverse.right-inverse-of f (just x)
                  | Inverse.left-inverse-of f (just (⇐ x))
          ⇒⇐ x | just x₁ | p | just x₂ | q | b | c = just-inj (≡.trans (≡.sym (Inverse.right-inverse-of f (just x₂))) (≡.trans (≡.cong to c) b))
          ⇒⇐ x | just x₁ | p | nothing | q | _ | _ = ⊥-elim (q ≡.refl)
          ⇒⇐ x | nothing | p | z       | q | _ | _ = ⊥-elim (p ≡.refl)

    module _ {A B : Set}
      (f : Maybe A ↔ Maybe B)
      (f-empty : Inverse.to f ⟨$⟩ nothing ≡ nothing) where

      tof-tot : ∀ x → Inverse.to f ⟨$⟩ just x ≢ nothing
      tof-tot x eq with Inverse.injective f (≡.trans eq (≡.sym f-empty))
      ... | ()

      f-empty' : Inverse.from f ⟨$⟩ nothing ≡ nothing
      f-empty' = ≡.trans (≡.sym (≡.cong (λ x → Inverse.from f ⟨$⟩ x) f-empty)) (Inverse.left-inverse-of f nothing)

      fof-tot : ∀ x → Inverse.from f ⟨$⟩ just x ≢ nothing
      fof-tot x eq with Inverse.injective (sym f) (≡.trans eq (≡.sym f-empty'))
      ... | ()

      iso : A ↔ B
      iso = CancelMaybe' f tof-tot fof-tot


    module _ {A B : Set}
      (f : Maybe A ↔ Maybe B) where

      g : Maybe A ↔ Maybe B
      g = inverses (⇒) (⇐) ⇐⇒ ⇒⇐ where
          to = λ x → Inverse.to f ⟨$⟩ x
          from = λ x → Inverse.from f ⟨$⟩ x

          ⇒ : Maybe A → Maybe B
          ⇒ (just x) with to (just x)
          ... | nothing = to nothing
          ... | just y  = just y
          ⇒ nothing = nothing

          ⇐ : Maybe B → Maybe A
          ⇐ (just x) with from (just x)
          ... | nothing = from nothing
          ... | just y  = just y
          ⇐ nothing = nothing

          ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
          ⇐⇒ (just x) with to (just x) | Inverse.left-inverse-of f (just x)
          ⇐⇒ (just x) | just x₁ | p rewrite p = ≡.refl
          ⇐⇒ (just x) | nothing | p with to nothing | Inverse.left-inverse-of f nothing
          ⇐⇒ (just x₁) | nothing | p | just x | q rewrite q = p
          ⇐⇒ (just x) | nothing | p | nothing | q = ≡.trans (≡.sym q) p
          ⇐⇒ nothing = ≡.refl

          ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
          ⇒⇐ (just x) with from (just x) | Inverse.right-inverse-of f (just x)
          ⇒⇐ (just x) | just x₁ | p rewrite p = ≡.refl
          ⇒⇐ (just x) | nothing | p with from nothing | Inverse.right-inverse-of f nothing
          ⇒⇐ (just x₁) | nothing | p | just x | q rewrite q = p
          ⇒⇐ (just x) | nothing | p | nothing | q = ≡.trans (≡.sym q) p
          ⇒⇐ nothing = ≡.refl

      g-empty : Inverse.to g ⟨$⟩ nothing ≡ nothing
      g-empty = ≡.refl

      iso' : A ↔ B
      iso' = iso g g-empty
  CancelMaybe : ∀ {A B : Set} → Maybe A ↔ Maybe B → A ↔ B
  CancelMaybe f = iso' f

private
    Setoid₀ : ★ _
    Setoid₀ = Setoid L.zero L.zero

⊎-ICommutativeMonoid : CommutativeMonoid _ _
⊎-ICommutativeMonoid = record {
                         _≈_ = Inv.Inverse;
                         _∙_ = _⊎-setoid_;
                         ε = ≡.setoid ⊥;
                         isCommutativeMonoid = record
                            { isSemigroup = record
                              { isEquivalence = Inv.isEquivalence
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
      swap' : ∀ {A B} → A ⊎-setoid B FE.⟶ B ⊎-setoid A
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
                         _≈_ = Inv.Inverse;
                         _∙_ = _×-setoid_;
                         ε = ≡.setoid ⊤;
                         isCommutativeMonoid = record
                            { isSemigroup = record
                              { isEquivalence = Inv.isEquivalence
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
      swap' : ∀ {A B} → A ×-setoid B FE.⟶ B ×-setoid A
      swap' {A}{B} = record { _⟨$⟩_ = swap; cong = swap }

      inv : ∀ A B → ∀ x → Setoid._≈_ (A ×-setoid B) (swap' {B} {A} FE.∘ swap' {A} {B}⟨$⟩ x) x
      inv A B = λ x → Setoid.refl (A ×-setoid B)

×⊎-ICommutativeSemiring : CommutativeSemiring _ _
×⊎-ICommutativeSemiring = record
  { _≈_ = Inv.Inverse
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
      cong-from (₁∼₁ (B-rel , A-rel)) = ₁∼₁ B-rel , A-rel
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

module ×-CMon {a} = CommutativeMonoid (×-CommutativeMonoid FR.bijection a)
module ⊎-CMon {a} = CommutativeMonoid (⊎-CommutativeMonoid FR.bijection a)
module ×⊎° {a}    = CommutativeSemiring (×⊎-CommutativeSemiring FR.bijection a)

module ×-ICMon = CommutativeMonoid ×-ICommutativeMonoid
module ⊎-ICMon = CommutativeMonoid ⊎-ICommutativeMonoid
module ×⊎°I    = CommutativeSemiring ×⊎-ICommutativeSemiring

lift-⊎ : ∀ {A B : Set} → Inv.Inverse ((≡.setoid A) ⊎-setoid (≡.setoid B)) (≡.setoid (A ⊎ B))
lift-⊎ {A}{B} = record
  { to = record
    { _⟨$⟩_ = λ x → x
    ; cong = cong
    }
  ; from = record
    { _⟨$⟩_ = λ x → x
    ; cong = λ x → Setoid.reflexive (≡.setoid A ⊎-setoid ≡.setoid B) x
    }
  ; inverse-of = record
    { left-inverse-of = λ x → Setoid.refl (≡.setoid A ⊎-setoid ≡.setoid B)
    ; right-inverse-of = λ x → Setoid.refl (≡.setoid (A ⊎ B))
    }
  } where
    cong : Setoid._≈_ (≡.setoid A ⊎-setoid ≡.setoid B)  =[ _ ]⇒ Setoid._≈_ (≡.setoid (A ⊎ B))
    cong (₁∼₂ ())
    cong (₁∼₁ x∼₁y) = ≡.cong inj₁ x∼₁y
    cong (₂∼₂ x∼₂y) = ≡.cong inj₂ x∼₂y

swap-iso : ∀ {a b} {A : ★ a} {B : ★ b} → (A × B) ↔ (B × A)
swap-iso = inverses swap swap (λ _ → ≡.refl) (λ _ → ≡.refl)

Maybe↔Lift⊤⊎ : ∀ {ℓ a} {A : ★ a} → Maybe A ↔ (Lift {ℓ = ℓ} ⊤ ⊎ A)
Maybe↔Lift⊤⊎
  = inverses (maybe inj₂ (inj₁ _))
             [ F.const nothing , just ]
             (maybe (λ _ → ≡.refl) ≡.refl)
             [ (λ _ → ≡.refl) , (λ _ → ≡.refl) ]

Maybe↔⊤⊎ : ∀ {a} {A : ★ a} → Maybe A ↔ (⊤ ⊎ A)
Maybe↔⊤⊎
  = inverses (maybe inj₂ (inj₁ _))
             [ F.const nothing , just ]
             (maybe (λ _ → ≡.refl) ≡.refl)
             [ (λ _ → ≡.refl) , (λ _ → ≡.refl) ]

Maybe-cong : ∀ {a b} {A : ★ a} {B : ★ b} → A ↔ B → Maybe A ↔ Maybe B
Maybe-cong A↔B = sym Maybe↔⊤⊎ ∘ id ⊎-cong A↔B ∘ Maybe↔⊤⊎

Maybe∘Maybe^↔Maybe^∘Maybe : ∀ {a} {A : ★ a} n → Maybe (Maybe^ n A) ↔ Maybe^ n (Maybe A)
Maybe∘Maybe^↔Maybe^∘Maybe zero    = id
Maybe∘Maybe^↔Maybe^∘Maybe (suc n) = Maybe-cong (Maybe∘Maybe^↔Maybe^∘Maybe n)

Maybe^-cong : ∀ {a b} {A : ★ a} {B : ★ b} n → A ↔ B → Maybe^ n A ↔ Maybe^ n B
Maybe^-cong zero    = F.id
Maybe^-cong (suc n) = Maybe-cong F.∘ Maybe^-cong n

Vec0↔Lift⊤ : ∀ {a ℓ} {A : ★ a} → Vec A 0 ↔ Lift {_} {ℓ} ⊤
Vec0↔Lift⊤ = inverses _ (F.const []) (λ { [] → ≡.refl }) (λ _ → ≡.refl)

Vec0↔⊤ : ∀ {a} {A : ★ a} → Vec A 0 ↔ ⊤
Vec0↔⊤ = inverses _ (F.const []) (λ { [] → ≡.refl }) (λ _ → ≡.refl)

Vec∘suc↔A×Vec : ∀ {a} {A : ★ a} {n} → Vec A (suc n) ↔ (A × Vec A n)
Vec∘suc↔A×Vec
  = inverses (λ { (x ∷ xs) → x , xs }) (uncurry _∷_)
             (λ { (x ∷ xs) → ≡.refl }) (λ _ → ≡.refl)

infix 8 _^_

_^_ : ∀ {a} → ★ a → ℕ → ★ a
A ^ 0     = Lift ⊤
A ^ suc n = A × A ^ n

^↔Vec : ∀ {a} {A : ★ a} n → (A ^ n) ↔ Vec A n
^↔Vec zero    = sym Vec0↔Lift⊤
^↔Vec (suc n) = sym Vec∘suc↔A×Vec ∘ (id ×-cong (^↔Vec n))

Fin0↔⊥ : Fin 0 ↔ ⊥
Fin0↔⊥ = inverses (λ()) (λ()) (λ()) (λ())

Fin∘suc↔Maybe∘Fin : ∀ {n} → Fin (suc n) ↔ Maybe (Fin n)
Fin∘suc↔Maybe∘Fin {n}
  = inverses to (maybe suc zero)
             (λ { zero → ≡.refl ; (suc n) → ≡.refl })
             (maybe (λ _ → ≡.refl) ≡.refl)
  where to : Fin (suc n) → Maybe (Fin n)
        to zero = nothing
        to (suc n) = just n

Lift↔id : ∀ {a} {A : ★ a} → Lift {a} {a} A ↔ A
Lift↔id = inverses lower lift (λ { (lift x) → ≡.refl }) (λ _ → ≡.refl)

⊤×A↔A : ∀ {A : ★₀} → (⊤ × A) ↔ A
⊤×A↔A = proj₁ ×-CMon.identity _ ∘ sym Lift↔id ×-cong id

A×⊤↔A : ∀ {A : ★₀} → (A × ⊤) ↔ A
A×⊤↔A = proj₂ ×-CMon.identity _ ∘ id ×-cong sym Lift↔id

⊥⊎A↔A : ∀ {A : ★₀} → (⊥ ⊎ A) ↔ A
⊥⊎A↔A = proj₁ ⊎-CMon.identity _ ∘ sym Lift↔id ⊎-cong id

A⊎⊥↔A : ∀ {A : ★₀} → (A ⊎ ⊥) ↔ A
A⊎⊥↔A = proj₂ ⊎-CMon.identity _ ∘ id ⊎-cong sym Lift↔id

⊥×A↔⊥ : ∀ {A : ★₀} → (⊥ × A) ↔ ⊥
⊥×A↔⊥ = Lift↔id ∘ proj₁ ×⊎°.zero _ ∘ sym (Lift↔id ×-cong id)

Maybe⊥↔⊤ : Maybe ⊥ ↔ ⊤
Maybe⊥↔⊤ = A⊎⊥↔A ∘ Maybe↔⊤⊎

Maybe^⊥↔Fin : ∀ n → Maybe^ n ⊥ ↔ Fin n
Maybe^⊥↔Fin zero    = sym Fin0↔⊥
Maybe^⊥↔Fin (suc n) = sym Fin∘suc↔Maybe∘Fin ∘ Maybe-cong (Maybe^⊥↔Fin n)

Maybe^⊤↔Fin1+ : ∀ n → Maybe^ n ⊤ ↔ Fin (suc n)
Maybe^⊤↔Fin1+ n = Maybe^⊥↔Fin (suc n) ∘ sym (Maybe∘Maybe^↔Maybe^∘Maybe n) ∘ Maybe^-cong n (sym Maybe⊥↔⊤)

Maybe-⊎ : ∀ {a} {A B : ★ a} → (Maybe A ⊎ B) ↔ Maybe (A ⊎ B)
Maybe-⊎ {a} = sym Maybe↔Lift⊤⊎ ∘ ⊎-CMon.assoc (Lift {_} {a} ⊤) _ _ ∘ (Maybe↔Lift⊤⊎ ⊎-cong id)

Maybe^-⊎-+ : ∀ {A} m n → (Maybe^ m ⊥ ⊎ Maybe^ n A) ↔ Maybe^ (m + n) A
Maybe^-⊎-+ zero    n = ⊥⊎A↔A
Maybe^-⊎-+ (suc m) n = Maybe-cong (Maybe^-⊎-+ m n) ∘ Maybe-⊎

Fin-⊎-+ : ∀ m n → (Fin m ⊎ Fin n) ↔ Fin (m + n)
Fin-⊎-+ m n = Maybe^⊥↔Fin (m + n)
            ∘ Maybe^-⊎-+ m n
            ∘ sym (Maybe^⊥↔Fin m ⊎-cong Maybe^⊥↔Fin n)

Fin∘suc↔⊤⊎Fin : ∀ {n} → Fin (suc n) ↔ (⊤ ⊎ Fin n)
Fin∘suc↔⊤⊎Fin = Maybe↔⊤⊎ ∘ Fin∘suc↔Maybe∘Fin

Fin-×-* : ∀ m n → (Fin m × Fin n) ↔ Fin (m * n)
Fin-×-* zero n = (Fin 0 × Fin n) ↔⟨ Fin0↔⊥ ×-cong id ⟩ 
                 (⊥ × Fin n) ↔⟨ ⊥×A↔⊥ ⟩
                 ⊥ ↔⟨ sym Fin0↔⊥ ⟩
                 Fin 0 ∎
  where open EquationalReasoning hiding (sym)
Fin-×-* (suc m) n = (Fin (suc m) × Fin n) ↔⟨ Fin∘suc↔⊤⊎Fin ×-cong id ⟩
                    ((⊤ ⊎ Fin m) × Fin n) ↔⟨ ×⊎°.distribʳ (Fin n) ⊤ (Fin m) ⟩
                    ((⊤ × Fin n) ⊎ (Fin m × Fin n)) ↔⟨ ⊤×A↔A ⊎-cong Fin-×-* m n ⟩
                    (Fin n ⊎ Fin (m * n)) ↔⟨ Fin-⊎-+ n (m * n) ⟩
                    Fin (suc m * n) ∎
  where open EquationalReasoning hiding (sym)
