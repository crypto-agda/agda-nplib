{-# OPTIONS --without-K #-}
open import Type

open import Level.NP
open import HoTT
open import Function.NP
open import Function.Extensionality

open import Data.Maybe.NP using (Maybe ; just ; nothing ; maybe ; maybe′ ; just-injective)
open import Data.Zero using (𝟘 ; 𝟘-elim)
open import Data.One using (𝟙)
open import Data.Two using (𝟚 ; 0₂ ; 1₂ ; [0:_1:_]; twist)
open import Data.Fin as Fin using (Fin ; suc ; zero)
open import Data.Nat.NP as ℕ using (ℕ ; suc ; zero)
open import Data.Product.NP renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_])

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≢_ ; ap; coe; coe!; !_; _∙_; J ; inspect ; Reveal_is_ ; [_]; tr) renaming (refl to idp; cong₂ to ap₂; _≗_ to _∼_)

module Type.Identities where

open Equivalences


-- for use with ap₂ etc.
_⟶_ : ∀ {a b} → ★_ a → ★_ b → ★_ (b ⊔ a)
A ⟶ B = A → B

𝟚≃𝟙⊎𝟙 : 𝟚 ≃ (𝟙 ⊎ 𝟙)
𝟚≃𝟙⊎𝟙 = equiv [0: inl _ 1: inr _ ]
              [inl: const 0₂ ,inr: const 1₂ ]
              [inl: (λ _ → idp) ,inr: (λ _ → idp) ]
              [0: idp 1: idp ]

𝟚≡𝟙⊎𝟙 : {{_ : UA}} → 𝟚 ≡ (𝟙 ⊎ 𝟙)
𝟚≡𝟙⊎𝟙 = ua 𝟚≃𝟙⊎𝟙

module _ {{_ : UA}}{A : ★}{B C : A → ★} where
    Σ⊎-split : (Σ A (λ x → B x ⊎ C x)) ≡ (Σ A B ⊎ Σ A C)
    Σ⊎-split = ua (equiv (λ { (x , inl y) → inl (x , y)
                            ; (x , inr y) → inr (x , y) })
                         (λ { (inl (x , y)) → x , inl y
                            ; (inr (x , y)) → x , inr y })
                         (λ { (inl (x , y)) → idp
                            ; (inr (x , y)) → idp })
                         (λ { (x , inl y) → idp
                            ; (x , inr y) → idp }))

module _ {{_ : UA}}{A B : ★}{C : A ⊎ B → ★} where
    dist-⊎-Σ-equiv : Σ (A ⊎ B) C ≃ (Σ A (C ∘ inl) ⊎ Σ B (C ∘ inr))
    dist-⊎-Σ-equiv = equiv (λ { (inl x , y) → inl (x , y)
                              ; (inr x , y) → inr (x , y) })
                           [inl: (λ x → inl (fst x) , snd x)
                           ,inr: (λ x → inr (fst x) , snd x) ]
                           [inl: (λ x → idp) ,inr: (λ x → idp) ]
                           (λ { (inl x , y) → idp
                              ; (inr x , y) → idp })

    dist-⊎-Σ : Σ (A ⊎ B) C ≡ (Σ A (C ∘ inl) ⊎ Σ B (C ∘ inr))
    dist-⊎-Σ = ua dist-⊎-Σ-equiv

    module _{{_ : FunExt}} where
      dist-×-Π-equiv : Π (A ⊎ B) C ≃ (Π A (C ∘ inl) × Π B (C ∘ inr))
      dist-×-Π-equiv = equiv (λ f → f ∘ inl , f ∘ inr) (λ fg → [inl: fst fg ,inr: snd fg ])
                             (λ _ → idp) (λ _ → λ= [inl: (λ _ → idp) ,inr: (λ _ → idp) ])

      dist-×-Π : Π (A ⊎ B) C ≡ (Π A (C ∘ inl) × Π B (C ∘ inr))
      dist-×-Π = ua dist-×-Π-equiv

module _ {{_ : UA}}{A B : ★}{C : A → ★}{D : B → ★} where
    dist-⊎-Σ[] : (Σ (A ⊎ B) [inl: C ,inr: D ]) ≡ (Σ A C ⊎ Σ B D)
    dist-⊎-Σ[] = dist-⊎-Σ

    module _{{_ : FunExt}} where
      dist-×-Π[] : (Π (A ⊎ B) [inl: C ,inr: D ]) ≡ (Π A C × Π B D)
      dist-×-Π[] = dist-×-Π

module _ {{_ : UA}}{A B C : ★} where
    dist-⊎-×-equiv : ((A ⊎ B) × C) ≃ (A × C ⊎ B × C)
    dist-⊎-×-equiv = equiv (λ { (inl x , y) → inl (x , y)
                              ; (inr x , y) → inr (x , y) })
                           [inl: (λ x → inl (fst x) , snd x)
                           ,inr: (λ x → inr (fst x) , snd x) ]
                           [inl: (λ x → idp) ,inr: (λ x → idp) ]
                           (λ { (inl x , y) → idp
                              ; (inr x , y) → idp })

    dist-⊎-× : ((A ⊎ B) × C) ≡ (A × C ⊎ B × C)
    dist-⊎-× = ua dist-⊎-×-equiv

    module _ {{_ : FunExt}} where
      dist-×-→-equiv : ((A ⊎ B) → C ) ≃ ((A → C) × (B → C))
      dist-×-→-equiv = equiv (λ f → f ∘ inl , f ∘ inr) (λ fg → [inl: fst fg ,inr: snd fg ])
                             (λ _ → idp) (λ _ → λ= [inl: (λ _ → idp) ,inr: (λ _ → idp) ])

      dist-×-→ : ((A ⊎ B) → C) ≡ ((A → C) × (B → C))
      dist-×-→ = ua dist-×-→-equiv

module _ {A : ★}{B : A → ★}{C : (x : A) → B x → ★} where
    Σ-assoc-equiv : (Σ A (λ x → Σ (B x) (C x))) ≃ (Σ (Σ A B) (uncurry C))
    Σ-assoc-equiv = equiv (λ x → (fst x , fst (snd x)) , snd (snd x))
                          (λ x → fst (fst x) , snd (fst x) , snd x)
                          (λ y → idp)
                          (λ y → idp)

    Σ-assoc : {{_ : UA}} → (Σ A (λ x → Σ (B x) (C x))) ≡ (Σ (Σ A B) (uncurry C))
    Σ-assoc = ua Σ-assoc-equiv

module _ {A B : ★} where
    ×-comm-equiv : (A × B) ≃ (B × A)
    ×-comm-equiv = equiv swap swap (λ y → idp) (λ x → idp)

    ×-comm : {{_ : UA}} → (A × B) ≡ (B × A)
    ×-comm = ua ×-comm-equiv

    ⊎-comm-equiv : (A ⊎ B) ≃ (B ⊎ A)
    ⊎-comm-equiv = equiv [inl: inr ,inr: inl ]
                         [inl: inr ,inr: inl ]
                         [inl: (λ x → idp) ,inr: (λ x → idp) ]
                         [inl: (λ x → idp) ,inr: (λ x → idp) ]

    ⊎-comm : {{_ : UA}} → (A ⊎ B) ≡ (B ⊎ A)
    ⊎-comm = ua ⊎-comm-equiv

module _ {A B : ★}{C : A → B → ★} where
    ΠΠ-comm-equiv : ((x : A)(y : B) → C x y) ≃ ((y : B)(x : A) → C x y)
    ΠΠ-comm-equiv = equiv flip flip (λ _ → idp) (λ _ → idp)

    ΠΠ-comm : {{_ : UA}} → ((x : A)(y : B) → C x y) ≡ ((y : B)(x : A) → C x y)
    ΠΠ-comm = ua ΠΠ-comm-equiv

    ΣΣ-comm-equiv : (Σ A λ x → Σ B λ y → C x y) ≃ (Σ B λ y → Σ A λ x → C x y)
    ΣΣ-comm-equiv = equiv (λ { (x , y , z) → y , x , z })
                          (λ { (x , y , z) → y , x , z })
                          (λ _ → idp)
                          (λ _ → idp)

    ΣΣ-comm : {{_ : UA}} → (Σ A λ x → Σ B λ y → C x y) ≡ (Σ B λ y → Σ A λ x → C x y)
    ΣΣ-comm = ua ΣΣ-comm-equiv

module _ {A B C : ★} where
    ×-assoc : {{_ : UA}} → (A × (B × C)) ≡ ((A × B) × C)
    ×-assoc = Σ-assoc

    ⊎-assoc-equiv : (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
    ⊎-assoc-equiv = equiv [inl: inl ∘ inl ,inr: [inl: inl ∘ inr ,inr: inr ] ]
                          [inl: [inl: inl ,inr: inr ∘ inl ] ,inr: inr ∘ inr ]
                          [inl: [inl: (λ x → idp) ,inr: (λ x → idp) ] ,inr: (λ x → idp) ]
                          [inl: (λ x → idp) ,inr: [inl: (λ x → idp) ,inr: (λ x → idp) ] ]

    ⊎-assoc : {{_ : UA}} → (A ⊎ (B ⊎ C)) ≡ ((A ⊎ B) ⊎ C)
    ⊎-assoc = ua ⊎-assoc-equiv

module _ {{_ : UA}}{{_ : FunExt}}(A : 𝟘 → ★) where
    Π𝟘-uniq : Π 𝟘 A ≡ 𝟙
    Π𝟘-uniq = ua (equiv _ (λ _ ()) (λ _ → idp) (λ _ → λ= (λ())))

module _ {{_ : UA}}(A : 𝟙 → ★) where
    Π𝟙-uniq : Π 𝟙 A ≡ A _
    Π𝟙-uniq = ua (equiv (λ f → f _) (λ x _ → x) (λ _ → idp) (λ _ → idp))

module _ {{_ : UA}}(A : ★) where
    Π𝟙-uniq′ : (𝟙 → A) ≡ A
    Π𝟙-uniq′ = Π𝟙-uniq (λ _ → A)

module _ {{_ : UA}}{{_ : FunExt}}(A : ★) where
    Π𝟘-uniq′ : (𝟘 → A) ≡ 𝟙
    Π𝟘-uniq′ = Π𝟘-uniq (λ _ → A)

    𝟘→A↔𝟙 = Π𝟘-uniq′

module _ {{_ : FunExt}}(F G : 𝟘 → ★) where
    -- also by Π𝟘-uniq twice
    Π𝟘-uniq' : Π 𝟘 F ≡ Π 𝟘 G
    Π𝟘-uniq' = Π=′ 𝟘 (λ())

module _ {A : 𝟘 → ★} where
    Σ𝟘-fst-equiv : Σ 𝟘 A ≃ 𝟘
    Σ𝟘-fst-equiv = equiv fst (λ()) (λ()) (λ { (() , _) })

    Σ𝟘-fst : {{_ : UA}} → Σ 𝟘 A ≡ 𝟘
    Σ𝟘-fst = ua Σ𝟘-fst-equiv

module _ {A : 𝟙 → ★} where
    Σ𝟙-snd-equiv : Σ 𝟙 A ≃ A _
    Σ𝟙-snd-equiv = equiv snd (_,_ _) (λ _ → idp) (λ _ → idp)

    Σ𝟙-snd : {{_ : UA}} → Σ 𝟙 A ≡ A _
    Σ𝟙-snd = ua Σ𝟙-snd-equiv

module _ {A : ★} where
    ⊎𝟘-inl-equiv : A ≃ (A ⊎ 𝟘)
    ⊎𝟘-inl-equiv = equiv inl [inl: id ,inr: (λ()) ] [inl: (λ _ → idp) ,inr: (λ()) ] (λ _ → idp)

    ⊎𝟘-inl : {{_ : UA}} → A ≡ (A ⊎ 𝟘)
    ⊎𝟘-inl = ua ⊎𝟘-inl-equiv

    𝟙×-snd : {{_ : UA}} → (𝟙 × A) ≡ A
    𝟙×-snd = Σ𝟙-snd

    ×𝟙-fst : {{_ : UA}} → (A × 𝟙) ≡ A
    ×𝟙-fst = ×-comm ∙ 𝟙×-snd

    -- old names
    A×𝟙≡A = ×𝟙-fst
    𝟙×A≡A = 𝟙×-snd

module _ {A : ★}{B : A → ★}{C : Σ A B → ★} where
    -- AC: Dependent axiom of choice
    -- In Type Theory it happens to be neither an axiom nor to be choosing anything.
    ΠΣ-comm-equiv : (∀ (x : A) → ∃ λ (y : B x) → C (x , y)) ≃ (∃ λ (f : Π A B) → ∀ (x : A) → C (x , f x))
    ΠΣ-comm-equiv = equiv (λ H → fst ∘ H , snd ∘ H) (λ H → < fst H , snd H >) (λ H → idp) (λ H → idp)

    ΠΣ-comm : {{_ : UA}}
            → (∀ (x : A) → ∃ λ (y : B x) → C (x , y)) ≡ (∃ λ (f : Π A B) → ∀ (x : A) → C (x , f x))
    ΠΣ-comm = ua ΠΣ-comm-equiv

module _ {A : 𝟚 → ★}{{_ : UA}}{{_ : FunExt}} where
  Σ𝟚-⊎ : Σ 𝟚 A ≡ (A 0₂ ⊎ A 1₂)
  Σ𝟚-⊎ = Σ-first 𝟚≃𝟙⊎𝟙 ∙ dist-⊎-Σ ∙ ap₂ _⊎_ Σ𝟙-snd Σ𝟙-snd

  Π𝟚-× : Π 𝟚 A ≡ (A 0₂ × A 1₂)
  Π𝟚-× = Π-first 𝟚≃𝟙⊎𝟙 ∙ dist-×-Π ∙ ap₂ _×_ (Π𝟙-uniq _) (Π𝟙-uniq _)

  Π𝟚F↔F₀×F₁ = Π𝟚-×

module _ {A : ★}{{_ : UA}}{{_ : FunExt}} where
  Σ𝟚-⊎′ : 𝟚 × A ≡ (A ⊎ A)
  Σ𝟚-⊎′ = Σ𝟚-⊎

  𝟚→A↔A×A : (𝟚 → A) ↔ (A × A)
  𝟚→A↔A×A

module _ where

  private
    maybe-elim : {X : Set}(m : Maybe X) → m ≢ nothing → X
    maybe-elim {X} m = maybe {B = λ m' → m' ≢ _ → _} (λ x _ → x) (λ e → 𝟘-elim (e idp)) m

    maybe-elim-just : {X : Set}(m : Maybe X)(p : m ≢ nothing)
      → just (maybe-elim m p) ≡ m
    maybe-elim-just (just x) p = idp
    maybe-elim-just nothing p = 𝟘-elim (p idp)

    maybe-elim-cong : ∀ {X : Set}{m m' : Maybe X}{p p'} → m ≡ m'
      → maybe-elim m p ≡ maybe-elim m' p'
    maybe-elim-cong {m = just x} idp = idp
    maybe-elim-cong {m = nothing} {p = p} idp = 𝟘-elim (p idp)

    not-just : {X : Set}{x : X} → _≢_ {A = Maybe X} (just x) nothing
    not-just ()

    !!-p : ∀ {x}{X : Set x}{x y : X}(p : x ≡ y) → ! (! p) ≡ p
    !!-p idp = idp

    !∙ : ∀ {ℓ}{A : Set ℓ}{x y : A}(p : x ≡ y) → ! p ∙ p ≡ idp
    !∙ idp = idp

    ∙! : ∀ {ℓ}{A : Set ℓ}{x y : A}(p : x ≡ y) → p ∙ ! p ≡ idp
    ∙! idp = idp


    record PreservePoint {A B : Set}(eq : Maybe A ≡ Maybe B) : Set where
      field
        coe-p : ∀ x → coe eq (just x) ≢ nothing
        coe!-p : ∀ x → coe! eq (just x) ≢ nothing
    open PreservePoint

    nothing-to-nothing : {A B : Set}(eq : Maybe A ≡ Maybe B)
      → coe eq nothing ≡ nothing → PreservePoint eq
    nothing-to-nothing eq n2n = record { coe-p = λ x p → not-just (coe-inj eq (p ∙ ! n2n))
                                       ; coe!-p = λ x p → not-just (coe-same (! !∙ eq) (just x)
                                                 ∙ ! (coe∘coe eq (! eq) (just x)) ∙ ap (coe eq) p ∙ n2n) }

    !-PP : ∀ {A B : Set} {e : Maybe A ≡ Maybe B} → PreservePoint e → PreservePoint (! e)
    !-PP {e = e} e-pp = record { coe-p = coe!-p e-pp
                               ; coe!-p = λ x p → coe-p e-pp x ( ap (λ X → coe X (just x)) (! !!-p e ) ∙ p) }

    to : ∀ {A B : Set}(e : Maybe A ≡ Maybe B) → PreservePoint e → A → B
    to e e-pp x = maybe-elim (coe e (just x)) (coe-p e-pp x)

    module _{A B : Set}{e : Maybe A ≡ Maybe B}{e' : Maybe B ≡ Maybe A}{ep ep'}(e'∙e=id : e' ∙ e ≡ idp)(x : B) where
      to-to : to e ep (to e' ep' x) ≡ x
      to-to = just-injective (ap just (maybe-elim-cong
                                                {m = coe e (just (maybe-elim (coe e' (just x)) _))}
                                                {m' = coe e (coe e' (just x))}
                                                {p' = λ q → not-just (! p ∙ q)} (ap (coe e) (maybe-elim-just _ _)))
                                      ∙ maybe-elim-just (coe e (coe e' (just x))) (λ q → not-just (! p ∙ q))
                                      ∙ p)
        where
          p : coe e (coe e' (just x)) ≡ just x
          p = coe∘coe e e' (just x) ∙ coe-same e'∙e=id (just x)

    cto : ∀ {A B : Set}(e : Maybe A ≡ Maybe B) → Maybe A → Maybe B
    cto e = maybe (maybe′ just (coe e nothing) ∘ coe e ∘ just) nothing

    module _ {A B : Set}{e : Maybe A ≡ Maybe B}{e' : Maybe B ≡ Maybe A}(e'∙e=id : e' ∙ e ≡ idp) where
      cto-cto : (x : Maybe B) → cto e (cto e' x) ≡ x
      cto-cto nothing = idp
      cto-cto (just x) with coe e' (just x) | coe∘coe e e' (just x) ∙ coe-same e'∙e=id (just x)
      cto-cto (just x) | just x₁ | p = ap (maybe just (coe e nothing)) p
      cto-cto (just x) | nothing | p with coe e' nothing
                                        | coe∘coe e e' nothing ∙ coe-same e'∙e=id nothing
      cto-cto (just x) | nothing | p | just y  | q = ap (maybe just (coe e nothing)) q ∙ p
      cto-cto (just x) | nothing | p | nothing | q = ! q ∙ p

  module _ {A B : Set} where
    create-PP-≃ : Maybe A ≡ Maybe B → Maybe A ≃ Maybe B
    create-PP-≃ e = equiv (cto e)
                          (cto (! e))
                          (cto-cto {e = e} {e' = ! e} (!∙ e))
                          (cto-cto {e = ! e}{e' = e} (∙! e))

    create-PP : {{_ : UA}} → Maybe A ≡ Maybe B → Σ (Maybe A ≡ Maybe B) PreservePoint
    create-PP eq = ua (create-PP-≃ eq) , nothing-to-nothing _ (coe-β (create-PP-≃ eq) nothing)

    Maybe-injective-PP : {{_ : UA}} → (e : Maybe A ≡ Maybe B) → PreservePoint e
      → A ≡ B
    Maybe-injective-PP e e-pp = ua
      (equiv (to e e-pp)
             (to (! e) (!-PP e-pp))
             (to-to {e = e} { ! e} {e-pp}{ !-PP e-pp} (!∙ e))
             (to-to {e = ! e} {e} { !-PP e-pp} {e-pp} (∙! e)))

    Maybe-injective : ∀ {{_ : UA}} → Maybe A ≡ Maybe B → A ≡ B
    Maybe-injective e = let (e' , e'-pp) = create-PP e in Maybe-injective-PP e' e'-pp


module _ {a}{A : ★_ a} where
  Maybe≃𝟙⊎ : Maybe A ≃ (𝟙 ⊎ A)
  Maybe≃𝟙⊎ = equiv (maybe inr (inl _)) [inl: const nothing ,inr: just ]
     [inl: (λ x → idp) ,inr: (λ x → idp) ]
     (maybe (λ x → idp) idp)

  Maybe≡𝟙⊎ : ∀ {{_ : UA}}→ Maybe A ≡ (𝟙 ⊎ A)
  Maybe≡𝟙⊎ = ua Maybe≃𝟙⊎

module _ {{_ : UA}} where
    Fin0≡𝟘 : Fin 0 ≡ 𝟘
    Fin0≡𝟘 = ua (equiv (λ ()) (λ ()) (λ ()) (λ ()))

    Fin1≡𝟙 : Fin 1 ≡ 𝟙
    Fin1≡𝟙 = ua (equiv _ (λ _ → zero) (λ _ → idp) β)
      where β : (_ : Fin 1) → _
            β zero = idp
            β (suc ())

module _ where
  isZero? : ∀ {n}{A : Fin (suc n) → Set} → ((i : Fin n) → A (suc i)) → A zero
    → (i : Fin (suc n)) → A i
  isZero? f x zero = x
  isZero? f x (suc i) = f i

  Fin∘suc≃𝟙⊎Fin : ∀ {n} → Fin (suc n) ≃ (𝟙 ⊎ Fin n)
  Fin∘suc≃𝟙⊎Fin = equiv (isZero? inr (inl _)) [inl: (λ _ → zero) ,inr: suc ]
    [inl: (λ _ → idp) ,inr: (λ _ → idp) ]
    (isZero? (λ _ → idp) idp)

  Fin∘suc≡𝟙⊎Fin : ∀ {{_ : UA}}{n} → Fin (suc n) ≡ (𝟙 ⊎ Fin n)
  Fin∘suc≡𝟙⊎Fin = ua Fin∘suc≃𝟙⊎Fin

Fin-⊎-+ : ∀ {{_ : UA}} {m n} → (Fin m ⊎ Fin n) ≡ Fin (m ℕ.+ n)
Fin-⊎-+ {zero} = ap₂ _⊎_ Fin0≡𝟘 idp ∙ ⊎-comm ∙ ! ⊎𝟘-inl
Fin-⊎-+ {suc m} = ap₂ _⊎_ Fin∘suc≡𝟙⊎Fin idp ∙ ! ⊎-assoc ∙ ap (_⊎_ 𝟙) Fin-⊎-+ ∙ ! Fin∘suc≡𝟙⊎Fin

Fin-×-* : ∀ {{_ : UA}} {m n} → (Fin m × Fin n) ≡ Fin (m ℕ.* n)
Fin-×-* {zero} = ap₂ _×_ Fin0≡𝟘 idp ∙ Σ𝟘-fst ∙ ! Fin0≡𝟘
Fin-×-* {suc m} = ap₂ _×_ Fin∘suc≡𝟙⊎Fin idp ∙ dist-⊎-× ∙ ap₂ _⊎_ Σ𝟙-snd Fin-×-* ∙ Fin-⊎-+

Fin-→-^ : ∀ {{_ : UA}}{{_ : FunExt}}{m n} → (Fin m → Fin n) ≡ Fin (n ℕ.^ m)
Fin-→-^ {zero} = ap₂ _⟶_ Fin0≡𝟘 idp ∙ Π𝟘-uniq′ _ ∙ ⊎𝟘-inl ∙ ap (_⊎_ 𝟙) (! Fin0≡𝟘)
                  ∙ ! Fin∘suc≡𝟙⊎Fin
Fin-→-^ {suc m} = ap₂ _⟶_ Fin∘suc≡𝟙⊎Fin idp ∙ dist-×-→ ∙ ap₂ _×_ (Π𝟙-uniq _) Fin-→-^ ∙ Fin-×-*

Fin∘suc≡Maybe∘Fin : ∀ {{_ : UA}}{n} → Fin (suc n) ≡ Maybe (Fin n)
Fin∘suc≡Maybe∘Fin = Fin∘suc≡𝟙⊎Fin ∙ ! Maybe≡𝟙⊎

Fin-injective : ∀ {{_ : UA}}{m n} → Fin m ≡ Fin n → m ≡ n
Fin-injective {zero} {zero} Finm≡Finn = idp
Fin-injective {zero} {suc n} Finm≡Finn = 𝟘-elim (coe (! Finm≡Finn ∙ Fin0≡𝟘) zero)
Fin-injective {suc m} {zero} Finm≡Finn = 𝟘-elim (coe (Finm≡Finn ∙ Fin0≡𝟘) zero)
Fin-injective {suc m} {suc n} Finm≡Finn
  = ap suc (Fin-injective (Maybe-injective
            (! Fin∘suc≡Maybe∘Fin ∙ Finm≡Finn ∙ Fin∘suc≡Maybe∘Fin)))

Fin⊎-injective : ∀ {{_ : UA}}{A B : Set} n → (Fin n ⊎ A) ≡ (Fin n ⊎ B) → A ≡ B
Fin⊎-injective zero    f = ⊎𝟘-inl ∙ ⊎-comm ∙  ap₂ _⊎_ (! Fin0≡𝟘) idp
                       ∙ f ∙ (ap₂ _⊎_ Fin0≡𝟘 idp ∙ ⊎-comm) ∙ ! ⊎𝟘-inl
Fin⊎-injective (suc n) f = Fin⊎-injective n (Maybe-injective
   (Maybe≡𝟙⊎ ∙ ⊎-assoc ∙ ap₂ _⊎_ (! Fin∘suc≡𝟙⊎Fin) idp ∙ f
   ∙ ap₂ _⊎_ Fin∘suc≡𝟙⊎Fin idp ∙ ! ⊎-assoc ∙ ! Maybe≡𝟙⊎))

module _ {{_ : UA}} where
    Lift≡id : ∀ {a} {A : ★_ a} → Lift {a} {a} A ≡ A
    Lift≡id = ua (equiv lower lift (λ _ → idp) (λ { (lift x) → idp }))

    Π𝟙F≡F : ∀ {ℓ} {F : 𝟙 → ★_ ℓ} → Π 𝟙 F ≡ F _
    Π𝟙F≡F = ua (equiv (λ x → x _) const (λ _ → idp) (λ _ → idp))

    𝟙→A≡A : ∀ {ℓ} {A : ★_ ℓ} → (𝟙 → A) ≡ A
    𝟙→A≡A = Π𝟙F≡F

    not-𝟚≡𝟚 : 𝟚 ≡ 𝟚
    not-𝟚≡𝟚 = twist

{-
TODO ?
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
-}
-- -}
-- -}
-- -}
-- -}
