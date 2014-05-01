-- {-# OPTIONS --without-K #-}
module Function.Related.TypeIsomorphisms.NP where

open import Level.NP
open import Algebra
import Algebra.FunctionProperties as FP
open import Type hiding (★)
-- open import Type.Identities
open import Function using (_ˢ_; const)

open import Data.Fin using (Fin; zero; suc; pred)
open import Data.Vec.NP using (Vec; []; _∷_; uncons; ∷-uncons)
open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_) renaming (_^_ to _**_)
open import Data.Maybe.NP
open import Data.Product.NP renaming (map to map×)
--open import Data.Product.N-ary
open import Data.Sum.NP renaming (map to map⊎)
open import Data.One
open import Data.Zero
open import Data.Two using (𝟚; 0₂; 1₂; proj; ✓; not; ≡→✓; ≡→✓not; ✓→≡; ✓not→≡ ; not-involutive; [0:_1:_])

import Function.NP as F
open F using (Π)
import Function.Equality as FE
open FE using (_⟨$⟩_)
open import Function.Related as FR
open import Function.Related.TypeIsomorphisms public
import Function.Inverse.NP as Inv
open Inv using (_↔_; _∘_; sym; id; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Relation.Binary
import Relation.Binary.Indexed as I
open import Data.Indexed using (_⊎°_)
open import Relation.Binary.Product.Pointwise public using (_×-cong_)
open import Relation.Binary.Sum public using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.Sum
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_ ; _≢_; _≗_)

module _ {A : Set} {p q : A → 𝟚} where
    ΣAP : Set
    ΣAP = Σ A (λ x → p x ≡ 1₂)

    ΣAQ : Set
    ΣAQ = Σ A (λ x → q x ≡ 1₂)

    ΣAP¬Q : Set
    ΣAP¬Q = Σ A (λ x → p x ≡ 1₂ × q x ≡ 0₂)

    ΣA¬PQ : Set
    ΣA¬PQ = Σ A (λ x → p x ≡ 0₂ × q x ≡ 1₂)

    {-
    module M
      (f : ΣAP → ΣAQ)
      (f-1 : ΣAQ → ΣAP)
      (f-1f : ∀ x → f-1 (f x) ≡ x)
      (ff-1 : ∀ x → f (f-1 x) ≡ x)
       where

      f' : ΣAP¬Q → ΣA¬PQ
      f' (x , (p , nq)) = let y = f (x , p) in proj₁ y , {!proj₂ y!} , (proj₂ y)

      f-1' : ΣA¬PQ → ΣAP¬Q
      f-1' = {!!}

      f-1f' : ∀ x → f-1' (f' x) ≡ x
      f-1f' = {!!}

      ff-1' : ∀ x → f' (f-1' x) ≡ x
      ff-1' = {!!}
    -}

    module Work-In-Progress
      (f' : ΣAP¬Q → ΣA¬PQ)
      (f-1' : ΣA¬PQ → ΣAP¬Q)
      (f-1f' : ∀ x → f-1' (f' x) ≡ x)
      (ff-1' : ∀ x → f' (f-1' x) ≡ x)
       where

      f   : (x : A) → p x ≡ 1₂ → q x ≡ 0₂ → ΣA¬PQ
      f x px qx = f' (x , (px , qx))

      f-1 : (x : A) → p x ≡ 0₂ → q x ≡ 1₂ → ΣAP¬Q
      f-1 x px qx = f-1' (x , (px , qx))

      f-1f : ∀ x px nqx →
             let y = proj₂ (f x px nqx) in proj₁ (f-1 (proj₁ (f x px nqx)) (proj₁ y) (proj₂ y)) ≡ x
      f-1f x px nqx = ≡.cong proj₁ (f-1f' (x , (px , nqx)))

      ff-1 : ∀ x px nqx →
             let y = proj₂ (f-1 x px nqx) in proj₁ (f (proj₁ (f-1 x px nqx)) (proj₁ y) (proj₂ y)) ≡ x
      ff-1 x px nqx = ≡.cong proj₁ (ff-1' (x , (px , nqx)))

      π' : (x : A) (px qx : 𝟚) → p x ≡ px → q x ≡ qx → A
      π' x 1₂ 1₂ px qx = x
      π' x 1₂ 0₂ px qx = proj₁ (f x px qx)
      π' x 0₂ 1₂ px qx = proj₁ (f-1 x px qx)
      π' x 0₂ 0₂ px qx = x

      π : A → A
      π x = π' x (p x) (q x) ≡.refl ≡.refl

      0≢1 : 0₂ ≢ 1₂
      0≢1 ()

      π01 : ∀ x px qx (ppx : p x ≡ px) (qqx : q x ≡ qx) (px0 : p x ≡ 0₂) (qx1 : q x ≡ 1₂) → π' x px qx ppx qqx ≡ π' x 0₂ 1₂ px0 qx1
      π01 x 1₂ _  ppx qqx px0 qx1 = 𝟘-elim (0≢1 (≡.trans (≡.sym px0) ppx))
      π01 x 0₂ 1₂ ppx qqx px0 qx1 = ≡.cong₂ (λ z1 z2 → proj₁ (f-1 x z1 z2)) (≡.proof-irrelevance ppx px0) (≡.proof-irrelevance qqx qx1)
      π01 x 0₂ 0₂ ppx qqx px0 qx1 = 𝟘-elim (0≢1 (≡.trans (≡.sym qqx) qx1))

      π10 : ∀ x px qx (ppx : p x ≡ px) (qqx : q x ≡ qx) (px1 : p x ≡ 1₂) (qx0 : q x ≡ 0₂) → π' x px qx ppx qqx ≡ π' x 1₂ 0₂ px1 qx0
      π10 x 0₂ _  ppx qqx px1 qx0 = 𝟘-elim (0≢1 (≡.trans (≡.sym ppx) px1))
      π10 x 1₂ 0₂ ppx qqx px1 qx0 = ≡.cong₂ (λ z1 z2 → proj₁ (f x z1 z2)) (≡.proof-irrelevance ppx px1) (≡.proof-irrelevance qqx qx0)
      π10 x 1₂ 1₂ ppx qqx px1 qx0 = 𝟘-elim (0≢1 (≡.trans (≡.sym qx0) qqx))

      π'bb : ∀ {b} x (px : p x ≡ b) (qx : q x ≡ b) ppx qqx ([ppx] : p x ≡ ppx) ([qqx] : q x ≡ qqx) → π' x ppx qqx [ppx] [qqx] ≡ x
      π'bb x px qx 1₂ 1₂ [ppx] [qqx] = ≡.refl
      π'bb x px qx 1₂ 0₂ [ppx] [qqx] = 𝟘-elim (0≢1 (≡.trans (≡.sym [qqx]) (≡.trans qx (≡.trans (≡.sym px) [ppx]))))
      π'bb x px qx 0₂ 1₂ [ppx] [qqx] = 𝟘-elim (0≢1 (≡.trans (≡.sym [ppx]) (≡.trans px (≡.trans (≡.sym qx) [qqx]))))
      π'bb x px qx 0₂ 0₂ [ppx] [qqx] = ≡.refl

      ππ' : ∀ x px qx [px] [qx] → let y = (π' x px qx [px] [qx]) in π' y (p y) (q y) ≡.refl ≡.refl ≡ x
      ππ' x 1₂ 1₂ px qx = π'bb x px qx (p x) (q x) ≡.refl ≡.refl
      ππ' x 1₂ 0₂ px qx = let fx = f x px qx in let pfx = proj₁ (proj₂ fx) in let qfx = proj₂ (proj₂ fx) in ≡.trans (π01 (proj₁ fx) (p (proj₁ fx)) (q (proj₁ fx)) ≡.refl ≡.refl pfx qfx) (f-1f x px qx)
      ππ' x 0₂ 1₂ px qx = let fx = f-1 x px qx in let pfx = proj₁ (proj₂ fx) in let qfx = proj₂ (proj₂ fx) in ≡.trans (π10 (proj₁ fx) (p (proj₁ fx)) (q (proj₁ fx)) ≡.refl ≡.refl pfx qfx) (ff-1 x px qx)
      ππ' x 0₂ 0₂ px qx = π'bb x px qx (p x) (q x) ≡.refl ≡.refl

      ππ : ∀ x → π (π x) ≡ x
      ππ x = ππ' x (p x) (q x) ≡.refl ≡.refl

      prop' : ∀ px qx x ([px] : p x ≡ px) ([qx] : q x ≡ qx) → q (π' x px qx [px] [qx]) ≡ px
      prop' 1₂ 1₂ x px qx = qx
      prop' 1₂ 0₂ x px qx = proj₂ (proj₂ (f x px qx))
      prop' 0₂ 1₂ x px qx = proj₂ (proj₂ (f-1 x px qx))
      prop' 0₂ 0₂ x px qx = qx

      prop : ∀ x → p x ≡ q (π x)
      prop x = ≡.sym (prop' (p x) (q x) x ≡.refl ≡.refl)

module _ {a b f} {A : Set a} {B : A → Set b}
         (F : (x : A) → B x → Set f) where

    -- Also called Axiom of dependent choice.
    dep-choice-iso : (Π A (λ x → Σ (B x) (F x)))
                   ↔ (Σ (Π A B) λ f → Π A (F ˢ f))
    dep-choice-iso = inverses (⇒) (uncurry <_,_>) (λ _ → ≡.refl) (λ _ → ≡.refl)
      where
        ⇒ = λ f → (λ x → proj₁ (f x)) , (λ x → proj₂ (f x))

Maybe-injective : ∀ {A B : Set} → Maybe A ↔ Maybe B → A ↔ B
Maybe-injective f = Iso.iso (g f) (g-empty f)
  module Maybe-injective where
    open Inverse using (injective; left-inverse-of; right-inverse-of)

    module _ {A B : Set}
      (f : Maybe A ↔ Maybe B)
      (tof-tot : ∀ x → to f (just x) ≢ nothing)
      (fof-tot : ∀ x → from f (just x) ≢ nothing) where

        CancelMaybe' : A ↔ B
        CancelMaybe' = inverses (⇒) (⇐) ⇐⇒ ⇒⇐ where

          ⇒ : _ → _
          ⇒ x with to f (just x) | tof-tot x
          ⇒ x | just y  | _ = y
          ⇒ x | nothing | p = 𝟘-elim (p ≡.refl)

          ⇐ : _ → _
          ⇐ x with from f (just x) | fof-tot x
          ⇐ x | just y  | p = y
          ⇐ x | nothing | p = 𝟘-elim (p ≡.refl)

          ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
          ⇐⇒ x with to f (just x)
                  | tof-tot x
                  | from f (just (⇒ x))
                  | fof-tot (⇒ x)
                  | left-inverse-of f (just x)
                  | right-inverse-of f (just (⇒ x))
          ⇐⇒ x | just x₁ | p | just x₂ | q | b | c  = just-injective (≡.trans (≡.sym (left-inverse-of f (just x₂))) (≡.trans (≡.cong (from f) c) b))
          ⇐⇒ x | just x₁ | p | nothing | q | _ | _  = 𝟘-elim (q ≡.refl)
          ⇐⇒ x | nothing | p | z       | q | _ | _  = 𝟘-elim (p ≡.refl)

          ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
          ⇒⇐ x with from f (just x)
                  | fof-tot x
                  | to f (just (⇐ x))
                  | tof-tot (⇐ x)
                  | right-inverse-of f (just x)
                  | left-inverse-of f (just (⇐ x))
          ⇒⇐ x | just x₁ | p | just x₂ | q | b | c = just-injective (≡.trans (≡.sym (right-inverse-of f (just x₂))) (≡.trans (≡.cong (to f) c) b))
          ⇒⇐ x | just x₁ | p | nothing | q | _ | _ = 𝟘-elim (q ≡.refl)
          ⇒⇐ x | nothing | p | z       | q | _ | _ = 𝟘-elim (p ≡.refl)

    module Iso {A B : Set}
      (f : Maybe A ↔ Maybe B)
      (f-empty : to f nothing ≡ nothing) where

      tof-tot : ∀ x → to f (just x) ≢ nothing
      tof-tot x eq with injective f (≡.trans eq (≡.sym f-empty))
      ... | ()

      f-empty' : from f nothing ≡ nothing
      f-empty' = ≡.trans (≡.sym (≡.cong (from f) f-empty)) (left-inverse-of f nothing)

      fof-tot : ∀ x → from f (just x) ≢ nothing
      fof-tot x eq with injective (sym f) (≡.trans eq (≡.sym f-empty'))
      ... | ()

      iso : A ↔ B
      iso = CancelMaybe' f tof-tot fof-tot

    module _ {A B : Set}
      (f : Maybe A ↔ Maybe B) where

      g : Maybe A ↔ Maybe B
      g = inverses (⇒) (⇐) ⇐⇒ ⇒⇐ where

          ⇒ : Maybe A → Maybe B
          ⇒ (just x) with to f (just x)
          ... | nothing = to f nothing
          ... | just y  = just y
          ⇒ nothing = nothing

          ⇐ : Maybe B → Maybe A
          ⇐ (just x) with from f (just x)
          ... | nothing = from f nothing
          ... | just y  = just y
          ⇐ nothing = nothing

          ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
          ⇐⇒ (just x) with to f (just x) | left-inverse-of f (just x)
          ⇐⇒ (just x) | just x₁ | p rewrite p = ≡.refl
          ⇐⇒ (just x) | nothing | p with to f nothing | left-inverse-of f nothing
          ⇐⇒ (just x) | nothing | p | just _ | q rewrite q = p
          ⇐⇒ (just x) | nothing | p | nothing | q = ≡.trans (≡.sym q) p
          ⇐⇒ nothing = ≡.refl

          ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
          ⇒⇐ (just x) with from f (just x) | right-inverse-of f (just x)
          ⇒⇐ (just x) | just x₁ | p rewrite p = ≡.refl
          ⇒⇐ (just x) | nothing | p with from f nothing | right-inverse-of f nothing
          ⇒⇐ (just x) | nothing | p | just _  | q rewrite q = p
          ⇒⇐ (just x) | nothing | p | nothing | q = ≡.trans (≡.sym q) p
          ⇒⇐ nothing = ≡.refl

      g-empty : to g nothing ≡ nothing
      g-empty = ≡.refl

private
    Setoid₀ : ★ _
    Setoid₀ = Setoid ₀ ₀

-- requires extensionality
module _ {a b c} {A : ★ a} {B : A → ★ b} {C : A → ★ c}
         (extB : {f g : Π A B} → (∀ x → f x ≡ g x) → f ≡ g)
         (extC : {f g : Π A C} → (∀ x → f x ≡ g x) → f ≡ g)
         (f : ∀ x → B x ↔ C x) where
  private
    left-f = Inverse.left-inverse-of F.∘ f
    right-f = Inverse.right-inverse-of F.∘ f
    ⇒ : Π A B → Π A C
    ⇒ g x = to (f x) (g x)
    ⇐ : Π A C → Π A B
    ⇐ g x = from (f x) (g x)
    ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
    ⇐⇒ g = extB λ x → left-f x (g x)
    ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
    ⇒⇐ g = extC λ x → right-f x (g x)

  fiber-iso : Π A B ↔ Π A C
  fiber-iso = inverses (⇒) (⇐) ⇐⇒ ⇒⇐

Σ≡↔𝟙 : ∀ {a} {A : ★ a} x → Σ A (_≡_ x) ↔ 𝟙
Σ≡↔𝟙 x = inverses (F.const _) (λ _ → _ , ≡.refl)
                  helper (λ _ → ≡.refl)
  where helper : (y : Σ _ (_≡_ x)) → (x , ≡.refl) ≡ y
        helper (.x , ≡.refl) = ≡.refl

module _ {a b c} {A : ★ a} {B : A → ★ b} {C : Σ A B → ★ c} where
    curried : Π (Σ A B) C ↔ Π A λ a → Π (B a) λ b → C (a , b)
    curried = inverses curry uncurry (λ _ → ≡.refl) (λ _ → ≡.refl)

module _ {a b c} {A : ★ a} {B : ★ b} {C : A → ★ c} (f : A ↔ B) where
  private
    left-f = Inverse.left-inverse-of f
    right-f = Inverse.right-inverse-of f
    coe : ∀ x → C x → C (from f (to f x))
    coe x = ≡.subst C (≡.sym (left-f x))
    ⇒ : Σ A C → Σ B (C F.∘ from f)
    ⇒ (x , p) = to f x , coe x p
    ⇐ : Σ B (C F.∘ from f) → Σ A C
    ⇐ = first (from f)
    ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
    ⇐⇒ (x , p) rewrite left-f x = ≡.refl
    ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
    ⇒⇐ p = mkΣ≡ (C F.∘ from f) (right-f (proj₁ p)) (helper p)
            where
                helper : ∀ p → ≡.subst (C F.∘ from f) (right-f (proj₁ p)) (coe (proj₁ (⇐ p)) (proj₂ (⇐ p))) ≡ proj₂ p
                helper p with to f (from f (proj₁ p)) | right-f (proj₁ p) | left-f (from f (proj₁ p))
                helper _ | ._ | ≡.refl | ≡.refl = ≡.refl
  first-iso : Σ A C ↔ Σ B (C F.∘ from f)
  first-iso = inverses (⇒) (⇐) ⇐⇒ ⇒⇐

module _ {a b c} {A : ★ a} {B : ★ b} {C : B → ★ c} (f : A ↔ B) where
  sym-first-iso : Σ A (C F.∘ to f) ↔ Σ B C
  sym-first-iso = sym (first-iso (sym f))

module _ {a b c} {A : ★ a} {B : A → ★ b} {C : A → ★ c} (f : ∀ x → B x ↔ C x) where
  private
    left-f = Inverse.left-inverse-of F.∘ f
    right-f = Inverse.right-inverse-of F.∘ f
    ⇒ : Σ A B → Σ A C
    ⇒ = second (to (f _))
    ⇐ : Σ A C → Σ A B
    ⇐ = second (from (f _))
    ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
    ⇐⇒ (x , y) rewrite left-f x y = ≡.refl
    ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
    ⇒⇐ (x , y) rewrite right-f x y = ≡.refl
  second-iso : Σ A B ↔ Σ A C
  second-iso = inverses (⇒) (⇐) ⇐⇒ ⇒⇐

module _ {a b} {A : ★ a} {B : ★ b} (f₀ f₁ : A ↔ B) where
  𝟚×-second-iso : (𝟚 × A) ↔ (𝟚 × B)
  𝟚×-second-iso = second-iso {A = 𝟚} {B = const A} {C = const B} (proj (f₀ , f₁))

module _ {a b c} {A : ★ a} {B : ★ b} {C : A ⊎ B → ★ c} where
  private
    S = Σ (A ⊎ B) C
    T = Σ A (C F.∘ inj₁) ⊎ Σ B (C F.∘ inj₂)
    ⇒ : S → T
    ⇒ (inj₁ x , y) = inj₁ (x , y)
    ⇒ (inj₂ x , y) = inj₂ (x , y)
    ⇐ : T → S
    ⇐ (inj₁ (x , y)) = inj₁ x , y
    ⇐ (inj₂ (x , y)) = inj₂ x , y
    ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
    ⇐⇒ (inj₁ _ , _) = ≡.refl
    ⇐⇒ (inj₂ _ , _) = ≡.refl
    ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
    ⇒⇐ (inj₁ _) = ≡.refl
    ⇒⇐ (inj₂ _) = ≡.refl

  Σ⊎-distrib : (Σ (A ⊎ B) C) ↔ (Σ A (C F.∘ inj₁) ⊎ Σ B (C F.∘ inj₂))
  Σ⊎-distrib = inverses (⇒) (⇐) ⇐⇒ ⇒⇐

module _ {a b c} {A : ★ a} {B : A → ★ b} {C : A → ★ c} where
  private
    S = Σ A (B ⊎° C)
    T = Σ A B ⊎ Σ A C
    ⇒ : S → T
    ⇒ (x , inj₁ y) = inj₁ (x , y)
    ⇒ (x , inj₂ y) = inj₂ (x , y)
    ⇐ : T → S
    ⇐ (inj₁ (x , y)) = x , inj₁ y
    ⇐ (inj₂ (x , y)) = x , inj₂ y
    ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
    ⇐⇒ (_ , inj₁ _) = ≡.refl
    ⇐⇒ (_ , inj₂ _) = ≡.refl
    ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
    ⇒⇐ (inj₁ _) = ≡.refl
    ⇒⇐ (inj₂ _) = ≡.refl

  Σ-⊎-hom : Σ A (B ⊎° C) ↔ (Σ A B ⊎ Σ A C)
  Σ-⊎-hom = inverses (⇒) (⇐) ⇐⇒ ⇒⇐

-- requires extensional equality
module _ {a b c} {A : ★ a} {B : ★ b} {C : A ⊎ B → ★ c}
         (ext : {f g : Π (A ⊎ B) C} → (∀ x → f x ≡ g x) → f ≡ g)
         where
  private
    S = Π (A ⊎ B) C
    T = Π A (C F.∘ inj₁) × Π B (C F.∘ inj₂)
    ⇒ : S → T
    ⇒ f = f F.∘ inj₁ , f F.∘ inj₂
    ⇐ : T → S
    ⇐ (f , g) = [ f , g ]
    ⇐⇒ : ∀ f x → ⇐ (⇒ f) x ≡ f x
    ⇐⇒ f (inj₁ x) = ≡.refl
    ⇐⇒ f (inj₂ y) = ≡.refl
    ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
    ⇒⇐ (f , g) = ≡.refl

  Π×-distrib : Π (A ⊎ B) C ↔ (Π A (C F.∘ inj₁) × Π B (C F.∘ inj₂))
  Π×-distrib = inverses (⇒) (⇐) (λ f → ext (⇐⇒ f)) ⇒⇐

⊎-ICommutativeMonoid : CommutativeMonoid _ _
⊎-ICommutativeMonoid = record {
                         _≈_ = Inv.Inverse;
                         _∙_ = _⊎-setoid_;
                         ε = ≡.setoid 𝟘;
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
  open FP (Inv.Inverse {f₁ = ₀}{f₂ = ₀})

  left-identity : LeftIdentity (≡.setoid 𝟘) _⊎-setoid_
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
            cong-to : Setoid._≈_ (≡.setoid 𝟘 ⊎-setoid A) =[ _ ]⇒ _≈_
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
                         ε = ≡.setoid 𝟙;
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
  open FP (Inv.Inverse {f₁ = ₀}{f₂ = ₀})

  left-identity : LeftIdentity (≡.setoid 𝟙) _×-setoid_
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
  ; 0# = ≡.setoid 𝟘
  ; 1# = ≡.setoid 𝟙
  ; isCommutativeSemiring = record
    { +-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid ⊎-ICommutativeMonoid
    ; *-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid ×-ICommutativeMonoid
    ; distribʳ = distribʳ
    ; zeroˡ = zeroˡ
    }
  }
  where
  open FP (Inv.Inverse {f₁ = ₀}{f₂ = ₀})

  distribʳ : _×-setoid_ DistributesOverʳ _⊎-setoid_
  distribʳ A B C = record
    { to = record
      { _⟨$⟩_ = uncurry [ curry inj₁ , curry inj₂ ]
      ; cong = cong-to
      }
    ; from = record
      { _⟨$⟩_ = frm
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

      frm : B' × A' ⊎ C' × A' → (B' ⊎ C') × A'
      frm = [ map× inj₁ F.id , map× inj₂ F.id ]

      cong-from : _≈_ ((B ×-setoid A) ⊎-setoid (C ×-setoid A)) =[ _ ]⇒ _≈_ ((B ⊎-setoid C) ×-setoid A)
      cong-from (₁∼₂ ())
      cong-from (₁∼₁ (B-rel , A-rel)) = ₁∼₁ B-rel , A-rel
      cong-from (₂∼₂ (C-rel , A-rel)) = ₂∼₂ C-rel , A-rel

  zeroˡ : LeftZero (≡.setoid 𝟘) _×-setoid_
  zeroˡ A = record
    { to = record
      { _⟨$⟩_ = proj₁
      ; cong = proj₁
      }
    ; from = record
      { _⟨$⟩_ = 𝟘-elim
      ; cong = λ { {()} x }
      }
    ; inverse-of = record
      { left-inverse-of = λ x → 𝟘-elim (proj₁ x)
      ; right-inverse-of = λ x → 𝟘-elim x
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

module _ {a b c} {A : ★ a} {B : ★ b} {C : A × B → ★ c} where
  Σ×-swap : Σ (A × B) C ↔ Σ (B × A) (C F.∘ swap)
  Σ×-swap = first-iso swap-iso

Maybe↔Lift𝟙⊎ : ∀ {ℓ a} {A : ★ a} → Maybe A ↔ (Lift {ℓ = ℓ} 𝟙 ⊎ A)
Maybe↔Lift𝟙⊎
  = inverses (maybe inj₂ (inj₁ _))
             [ F.const nothing , just ]
             (maybe (λ _ → ≡.refl) ≡.refl)
             [ (λ _ → ≡.refl) , (λ _ → ≡.refl) ]

Maybe↔𝟙⊎ : ∀ {a} {A : ★ a} → Maybe A ↔ (𝟙 ⊎ A)
Maybe↔𝟙⊎
  = inverses (maybe inj₂ (inj₁ _))
             [ F.const nothing , just ]
             (maybe (λ _ → ≡.refl) ≡.refl)
             [ (λ _ → ≡.refl) , (λ _ → ≡.refl) ]

Maybe-cong : ∀ {a b} {A : ★ a} {B : ★ b} → A ↔ B → Maybe A ↔ Maybe B
Maybe-cong A↔B = sym Maybe↔𝟙⊎ ∘ id ⊎-cong A↔B ∘ Maybe↔𝟙⊎

Maybe∘Maybe^↔Maybe^∘Maybe : ∀ {a} {A : ★ a} n → Maybe (Maybe^ n A) ↔ Maybe^ n (Maybe A)
Maybe∘Maybe^↔Maybe^∘Maybe zero    = id
Maybe∘Maybe^↔Maybe^∘Maybe (suc n) = Maybe-cong (Maybe∘Maybe^↔Maybe^∘Maybe n)

Maybe^-cong : ∀ {a b} {A : ★ a} {B : ★ b} n → A ↔ B → Maybe^ n A ↔ Maybe^ n B
Maybe^-cong zero    = F.id
Maybe^-cong (suc n) = Maybe-cong F.∘ Maybe^-cong n

Vec0↔Lift𝟙 : ∀ {a ℓ} {A : ★ a} → Vec A 0 ↔ Lift {_} {ℓ} 𝟙
Vec0↔Lift𝟙 = inverses _ (F.const []) (λ { [] → ≡.refl }) (λ _ → ≡.refl)

Vec0↔𝟙 : ∀ {a} {A : ★ a} → Vec A 0 ↔ 𝟙
Vec0↔𝟙 = inverses _ (F.const []) (λ { [] → ≡.refl }) (λ _ → ≡.refl)

Vec∘suc↔A×Vec : ∀ {a} {A : ★ a} {n} → Vec A (suc n) ↔ (A × Vec A n)
Vec∘suc↔A×Vec
  = inverses uncons (uncurry _∷_) ∷-uncons (λ _ → ≡.refl)

infix 8 _^_

_^_ : ∀ {a} → ★ a → ℕ → ★ a
A ^ 0     = Lift 𝟙
A ^ suc n = A × A ^ n

^↔Vec : ∀ {a} {A : ★ a} n → (A ^ n) ↔ Vec A n
^↔Vec zero    = sym Vec0↔Lift𝟙
^↔Vec (suc n) = sym Vec∘suc↔A×Vec ∘ (id ×-cong (^↔Vec n))

Fin0↔𝟘 : Fin 0 ↔ 𝟘
Fin0↔𝟘 = inverses (λ()) (λ()) (λ()) (λ())

Fin1↔𝟙 : Fin 1 ↔ 𝟙
Fin1↔𝟙 = inverses _ (λ _ → zero) ⇐⇒ (λ _ → ≡.refl)
  where ⇐⇒ : (_ : Fin 1) → _
        ⇐⇒ zero = ≡.refl
        ⇐⇒ (suc ())

Fin∘suc↔Maybe∘Fin : ∀ {n} → Fin (suc n) ↔ Maybe (Fin n)
Fin∘suc↔Maybe∘Fin {n}
  = inverses to' (maybe suc zero)
             (λ { zero → ≡.refl ; (suc n) → ≡.refl })
             (maybe (λ _ → ≡.refl) ≡.refl)
  where to' : Fin (suc n) → Maybe (Fin n)
        to' zero = nothing
        to' (suc n) = just n

Fin-injective : ∀ {m n} → Fin m ↔ Fin n → m ≡ n
Fin-injective = go _ _ where
    go : ∀ m n → Fin m ↔ Fin n → m ≡ n
    go zero    zero    iso = ≡.refl
    go zero    (suc n) iso with from iso zero
    ...                       | ()
    go (suc m) zero    iso with to iso zero
    ...                       | ()
    go (suc m) (suc n) iso = ≡.cong suc (go m n (Maybe-injective (Fin∘suc↔Maybe∘Fin ∘ iso ∘ sym Fin∘suc↔Maybe∘Fin)))

Lift↔id : ∀ {a} {A : ★ a} → Lift {a} {a} A ↔ A
Lift↔id = inverses lower lift (λ { (lift x) → ≡.refl }) (λ _ → ≡.refl)

𝟙×A↔A : ∀ {A : ★₀} → (𝟙 × A) ↔ A
𝟙×A↔A = proj₁ ×-CMon.identity _ ∘ sym Lift↔id ×-cong id

A×𝟙↔A : ∀ {A : ★₀} → (A × 𝟙) ↔ A
A×𝟙↔A = proj₂ ×-CMon.identity _ ∘ id ×-cong sym Lift↔id

Π𝟙F↔F : ∀ {ℓ} {F : 𝟙 → ★_ ℓ} → Π 𝟙 F ↔ F _
Π𝟙F↔F = inverses (λ x → x _) const (λ _ → ≡.refl) (λ _ → ≡.refl)

𝟙→A↔A : ∀ {ℓ} {A : ★_ ℓ} → (𝟙 → A) ↔ A
𝟙→A↔A = Π𝟙F↔F

not-𝟚↔𝟚 : 𝟚 ↔ 𝟚
not-𝟚↔𝟚 = inverses not not not-involutive not-involutive

≡-iso : ∀ {ℓ ℓ'}{A : ★_ ℓ}{B : ★_ ℓ'}{x y : A} → (π : A ↔ B) → (x ≡ y) ↔ (to π x ≡ to π y)
≡-iso {x = x}{y} π = inverses (≡.cong (to π))
                              (λ p → ≡.trans (≡.sym (Inverse.left-inverse-of π x))
                                    (≡.trans (≡.cong (from π) p)
                                             (Inverse.left-inverse-of π y)))
                              (λ x → ≡.proof-irrelevance _ x) (λ x → ≡.proof-irrelevance _ x)

-- requires extensionality
module _ {a} {A : ★_ a} (ext𝟘 : (f g : 𝟘 → A) → f ≡ g) where
    𝟘→A↔𝟙 : (𝟘 → A) ↔ 𝟙
    𝟘→A↔𝟙 = inverses _ (λ _ ()) (λ h → ext𝟘 _ h) (λ _ → ≡.refl)

-- requires extensionality
module _ {ℓ} {F : 𝟘 → ★_ ℓ} (ext𝟘 : (f g : Π 𝟘 F) → f ≡ g) where
    Π𝟘↔𝟙 : Π 𝟘 F ↔ 𝟙
    Π𝟘↔𝟙 = inverses _ (λ _ ()) (λ h → ext𝟘 _ h) (λ _ → ≡.refl)

module _ {ℓ} {F : 𝟚 → ★_ ℓ} (ext𝟚 : {f g : Π 𝟚 F} → (∀ x → f x ≡ g x) → f ≡ g) where
    Π𝟚F↔F₀×F₁ : Π 𝟚 F ↔ (F 0₂ × F 1₂)
    Π𝟚F↔F₀×F₁ = inverses (λ f → f 0₂ , f 1₂) proj
                         (λ f → ext𝟚 (λ { 0₂ → ≡.refl ; 1₂ → ≡.refl }))
                         (λ _ → ≡.refl)

module _ {ℓ} {A : ★_ ℓ} (ext𝟚 : {f g : 𝟚 → A} → f ≗ g → f ≡ g) where
    𝟚→A↔A×A : (𝟚 → A) ↔ (A × A)
    𝟚→A↔A×A = Π𝟚F↔F₀×F₁ ext𝟚

𝟘⊎A↔A : ∀ {A : ★₀} → (𝟘 ⊎ A) ↔ A
𝟘⊎A↔A = proj₁ ⊎-CMon.identity _ ∘ sym Lift↔id ⊎-cong id

A⊎𝟘↔A : ∀ {A : ★₀} → (A ⊎ 𝟘) ↔ A
A⊎𝟘↔A = proj₂ ⊎-CMon.identity _ ∘ id ⊎-cong sym Lift↔id

𝟘×A↔𝟘 : ∀ {A : ★₀} → (𝟘 × A) ↔ 𝟘
𝟘×A↔𝟘 = Lift↔id ∘ proj₁ ×⊎°.zero _ ∘ sym (Lift↔id ×-cong id)

Maybe𝟘↔𝟙 : Maybe 𝟘 ↔ 𝟙
Maybe𝟘↔𝟙 = A⊎𝟘↔A ∘ Maybe↔𝟙⊎

Maybe^𝟘↔Fin : ∀ n → Maybe^ n 𝟘 ↔ Fin n
Maybe^𝟘↔Fin zero    = sym Fin0↔𝟘
Maybe^𝟘↔Fin (suc n) = sym Fin∘suc↔Maybe∘Fin ∘ Maybe-cong (Maybe^𝟘↔Fin n)

Maybe^𝟙↔Fin1+ : ∀ n → Maybe^ n 𝟙 ↔ Fin (suc n)
Maybe^𝟙↔Fin1+ n = Maybe^𝟘↔Fin (suc n) ∘ sym (Maybe∘Maybe^↔Maybe^∘Maybe n) ∘ Maybe^-cong n (sym Maybe𝟘↔𝟙)

Maybe-⊎ : ∀ {a} {A B : ★ a} → (Maybe A ⊎ B) ↔ Maybe (A ⊎ B)
Maybe-⊎ {a} = sym Maybe↔Lift𝟙⊎ ∘ ⊎-CMon.assoc (Lift {_} {a} 𝟙) _ _ ∘ (Maybe↔Lift𝟙⊎ ⊎-cong id)

Maybe^-⊎-+ : ∀ {A} m n → (Maybe^ m 𝟘 ⊎ Maybe^ n A) ↔ Maybe^ (m + n) A
Maybe^-⊎-+ zero    n = 𝟘⊎A↔A
Maybe^-⊎-+ (suc m) n = Maybe-cong (Maybe^-⊎-+ m n) ∘ Maybe-⊎

Σ𝟘↔𝟘 : ∀ {a} (F : 𝟘 → ★_ a) → Σ 𝟘 F ↔ 𝟘
Σ𝟘↔𝟘 F = inverses proj₁ (λ ()) (λ { ((), _) }) (λ ())

Σ𝟚↔⊎ : ∀ {a} (F : 𝟚 → ★_ a) → Σ 𝟚 F ↔ (F 0₂ ⊎ F 1₂)
Σ𝟚↔⊎ F = inverses (⇒) (⇐) ⇐⇒ ⇒⇐
  where
    ⇒ : (x : Σ _ _) → _
    ⇒ (0₂ , p) = inj₁ p
    ⇒ (1₂ , p) = inj₂ p
    ⇐ : (x : _ ⊎ _) → _
    ⇐ (inj₁ x) = 0₂ , x
    ⇐ (inj₂ y) = 1₂ , y

    ⇐⇒ : (_ : Σ _ _) → _
    ⇐⇒ (0₂ , p) = ≡.refl
    ⇐⇒ (1₂ , p) = ≡.refl
    ⇒⇐ : (_ : _ ⊎ _) → _
    ⇒⇐ (inj₁ _) = ≡.refl
    ⇒⇐ (inj₂ _) = ≡.refl

⊎⇿Σ2 : ∀ {ℓ} {A B : ★ ℓ} → (A ⊎ B) ↔ Σ 𝟚 [0: A 1: B ]
⊎⇿Σ2 {A = A} {B} = inverses (⇒) (⇐) ⇐⇒ ⇒⇐
  where
    ⇒ : A ⊎ B → _
    ⇒ (inj₁ x) = 0₂ , x
    ⇒ (inj₂ x) = 1₂ , x
    ⇐ : Σ _ _ → A ⊎ B
    ⇐ (0₂ , x) = inj₁ x
    ⇐ (1₂ , x) = inj₂ x
    ⇐⇒ : (_ : _ ⊎ _) → _
    ⇐⇒ (inj₁ x) = ≡.refl
    ⇐⇒ (inj₂ x) = ≡.refl
    ⇒⇐ : (_ : Σ _ _) → _
    ⇒⇐ (0₂ , x) = ≡.refl
    ⇒⇐ (1₂ , x) = ≡.refl

𝟚↔𝟙⊎𝟙 : 𝟚 ↔ (𝟙 ⊎ 𝟙)
𝟚↔𝟙⊎𝟙 = inverses (proj (inj₁ _ , inj₂ _)) [ F.const 0₂ , F.const 1₂ ] ⇐⇒ ⇒⇐
  where
  ⇐⇒ : (_ : 𝟚) → _
  ⇐⇒ 0₂ = ≡.refl
  ⇐⇒ 1₂ = ≡.refl
  ⇒⇐ : (_ : 𝟙 ⊎ 𝟙) → _
  ⇒⇐ (inj₁ _) = ≡.refl
  ⇒⇐ (inj₂ _) = ≡.refl

Fin-⊎-+ : ∀ m n → (Fin m ⊎ Fin n) ↔ Fin (m + n)
Fin-⊎-+ m n = Maybe^𝟘↔Fin (m + n)
            ∘ Maybe^-⊎-+ m n
            ∘ sym (Maybe^𝟘↔Fin m ⊎-cong Maybe^𝟘↔Fin n)

Fin∘suc↔𝟙⊎Fin : ∀ {n} → Fin (suc n) ↔ (𝟙 ⊎ Fin n)
Fin∘suc↔𝟙⊎Fin = Maybe↔𝟙⊎ ∘ Fin∘suc↔Maybe∘Fin

Fin↔𝟙⊎^𝟘 : ∀ n → Fin n ↔ 𝟙⊎^ n
Fin↔𝟙⊎^𝟘 zero    = Fin0↔𝟘
Fin↔𝟙⊎^𝟘 (suc n) = Inv.id ⊎-cong Fin↔𝟙⊎^𝟘 n Inv.∘ Fin∘suc↔𝟙⊎Fin

Fin-×-* : ∀ m n → (Fin m × Fin n) ↔ Fin (m * n)
Fin-×-* zero n = (Fin 0 × Fin n) ↔⟨ Fin0↔𝟘 ×-cong id ⟩
                 (𝟘 × Fin n) ↔⟨ 𝟘×A↔𝟘 ⟩
                 𝟘 ↔⟨ sym Fin0↔𝟘 ⟩
                 Fin 0 ∎
  where open EquationalReasoning hiding (sym)
Fin-×-* (suc m) n = (Fin (suc m) × Fin n) ↔⟨ Fin∘suc↔𝟙⊎Fin ×-cong id ⟩
                    ((𝟙 ⊎ Fin m) × Fin n) ↔⟨ ×⊎°.distribʳ (Fin n) 𝟙 (Fin m) ⟩
                    ((𝟙 × Fin n) ⊎ (Fin m × Fin n)) ↔⟨ 𝟙×A↔A ⊎-cong Fin-×-* m n ⟩
                    (Fin n ⊎ Fin (m * n)) ↔⟨ Fin-⊎-+ n (m * n) ⟩
                    Fin (suc m * n) ∎
  where open EquationalReasoning hiding (sym)

Fin⊎-injective : ∀ {A B : Set} n → (Fin n ⊎ A) ↔ (Fin n ⊎ B) → A ↔ B
Fin⊎-injective zero    f = 𝟘⊎A↔A ∘ Fin0↔𝟘 ⊎-cong id ∘ f ∘ sym Fin0↔𝟘 ⊎-cong id ∘ sym 𝟘⊎A↔A
Fin⊎-injective (suc n) f =
  Fin⊎-injective n
    (Maybe-injective
       (sym Maybe↔𝟙⊎ ∘
        ⊎-CMon.assoc _ _ _ ∘
        Fin∘suc↔𝟙⊎Fin ⊎-cong id ∘
        f ∘
        sym Fin∘suc↔𝟙⊎Fin ⊎-cong id ∘
        sym (⊎-CMon.assoc _ _ _) ∘
        Maybe↔𝟙⊎))

-- -}
-- -}
-- -}
-- -}
