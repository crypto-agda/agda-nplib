{-# OPTIONS --without-K #-}
module HoTT where

open import Type
open import Level.NP
open import Function.NP
open import Function.Extensionality
open import Data.Zero using (𝟘)
open import Data.One using (𝟙)
open import Data.Product.NP renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_])
open import Relation.Binary using (Reflexive; Symmetric; Transitive)
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; ap; coe; coe!; !_; _∙_; J) renaming (subst to tr; refl to idp; cong₂ to ap₂; _≗_ to _∼_)

import Function.Inverse.NP as Inv
open Inv using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)

-- Contractible
module _ {a}(A : ★_ a) where
    Is-contr : ★_ a
    Is-contr = Σ A λ x → ∀ y → x ≡ y

module _ {a}{b}{A : ★_ a}{B : A → ★_ b} where
    pair= : ∀ {x y : Σ A B} → (p : fst x ≡ fst y) → tr B p (snd x) ≡ snd y → x ≡ y
    pair= idp = ap (_,_ _)
    snd= : ∀ {x : A} {y y' : B x} → y ≡ y' → _≡_ {A = Σ A B} (x , y) (x , y')
    snd= = pair= idp

    tr-snd= : ∀ {p}(P : Σ A B → ★_ p){x}{y₀ y₁ : B x}(y= : y₀ ≡ y₁)
            → tr P (snd= {x = x} y=) ∼ tr (P ∘ _,_ x) y=
    tr-snd= P idp p = idp
module _ {a}{b}{A : ★_ a}{B : ★_ b} where
    pair×= : ∀ {x x' : A}(p : x ≡ x')
               {y y' : B}(q : y ≡ y')
             → (x , y) ≡ (x' , y')
    pair×= idp q = snd= q

module _ {a}(A : ★_ a){b}{B₀ B₁ : A → ★_ b}(B : (x : A) → B₀ x ≡ B₁ x){{_ : FunExt}} where
    Σ=′ : Σ A B₀ ≡ Σ A B₁
    Σ=′ = ap (Σ A) (λ= B)

    Π=′ : Π A B₀ ≡ Π A B₁
    Π=′ = ap (Π A) (λ= B)

module _ {{_ : FunExt}} where
    Σ= : ∀ {a}{A₀ A₁ : ★_ a}{b}{B₀ : A₀ → ★_ b}{B₁ : A₁ → ★_ b}
           (A : A₀ ≡ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (coe A x))
         → Σ A₀ B₀ ≡ Σ A₁ B₁
    Σ= idp B = Σ=′ _ B

    Π= : ∀ {a}{A₀ A₁ : ★_ a}{b}{B₀ : A₀ → ★_ b}{B₁ : A₁ → ★_ b}
           (A : A₀ ≡ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (coe A x))
         → Π A₀ B₀ ≡ Π A₁ B₁
    Π= idp B = Π=′ _ B

module _ {a}{A₀ A₁ : ★_ a}{b}{B₀ B₁ : ★_ b}(A= : A₀ ≡ A₁)(B= : B₀ ≡ B₁) where
    ×= : (A₀ × B₀) ≡ (A₁ × B₁)
    ×= = ap₂ _×_ A= B=

    ⊎= : (A₀ ⊎ B₀) ≡ (A₁ ⊎ B₁)
    ⊎= = ap₂ _⊎_ A= B=

module Equivalences where

  module _ {a b}{A : ★_ a}{B : ★_ b} where
    _LeftInverseOf_ : (B → A) → (A → B) → ★_ a
    linv LeftInverseOf f = ∀ x → linv (f x) ≡ x

    _RightInverseOf_ : (B → A) → (A → B) → ★_ b
    rinv RightInverseOf f = ∀ x → f (rinv x) ≡ x

    record Linv (f : A → B) : ★_(a ⊔ b) where
      field
        linv : B → A
        is-linv : ∀ x → linv (f x) ≡ x

    record Rinv (f : A → B) : ★_(a ⊔ b) where
      field
        rinv : B → A
        is-rinv : ∀ x → f (rinv x) ≡ x

    record Is-equiv (f : A → B) : ★_(a ⊔ b) where
      field
        linv : B → A
        is-linv : ∀ x → linv (f x) ≡ x
        rinv : B → A
        is-rinv : ∀ x → f (rinv x) ≡ x

      injective : ∀ {x y} → f x ≡ f y → x ≡ y
      injective {x} {y} p = !(is-linv x) ∙ ap linv p ∙ is-linv y

      surjective : ∀ y → ∃ λ x → f x ≡ y
      surjective y = rinv y , is-rinv y

  module _ {a b}{A : ★_ a}{B : ★_ b}{f : A → B}(fᴱ : Is-equiv f) where
      open Is-equiv fᴱ
      inv : B → A
      inv = linv ∘ f ∘ rinv

      inv-is-equiv : Is-equiv inv
      inv-is-equiv = record { linv = f
                         ; is-linv = λ x → ap f (is-linv (rinv x)) ∙ is-rinv x
                         ; rinv = f
                         ; is-rinv = λ x → ap linv (is-rinv (f x)) ∙ is-linv x }

  module _ {a b} where
    infix 4 _≃_
    _≃_ : ★_ a → ★_ b → ★_(a ⊔ b)
    A ≃ B = Σ (A → B) Is-equiv

  module _ {a}{A : ★_ a}(f : A → A)(f-inv : f LeftInverseOf f) where
      self-inv-is-equiv : Is-equiv f
      self-inv-is-equiv = record { linv = f ; is-linv = f-inv ; rinv = f ; is-rinv = f-inv }

      self-inv-equiv : A ≃ A
      self-inv-equiv = f , self-inv-is-equiv

  module _ {a}{A : ★_ a} where
    idᴱ : Is-equiv {A = A} id
    idᴱ = self-inv-is-equiv _ λ _ → idp

  module _ {a b c}{A : ★_ a}{B : ★_ b}{C : ★_ c}{g : B → C}{f : A → B} where
    _∘ᴱ_ : Is-equiv g → Is-equiv f → Is-equiv (g ∘ f)
    gᴱ ∘ᴱ fᴱ = record { linv = F.linv ∘ G.linv ; is-linv = λ x → ap F.linv (G.is-linv (f x)) ∙ F.is-linv x
                      ; rinv = F.rinv ∘ G.rinv ; is-rinv = λ x → ap g (F.is-rinv _) ∙ G.is-rinv x }
      where
        module G = Is-equiv gᴱ
        module F = Is-equiv fᴱ

  module _ {a b}{A : ★_ a}{B : ★_ b} where
    –> : (e : A ≃ B) → (A → B)
    –> e = fst e

    <– : (e : A ≃ B) → (B → A)
    <– e = Is-equiv.linv (snd e)

    <–-inv-l : (e : A ≃ B) (a : A)
              → (<– e (–> e a) ≡ a)
    <–-inv-l e a = Is-equiv.is-linv (snd e) a

    {-
    <–-inv-r : (e : A ≃ B) (b : B)
                → (–> e (<– e b) ≡ b)
    <–-inv-r e b = Is-equiv.is-rinv (snd e) b
    -}

    -- Equivalences are "injective"
    equiv-inj : (e : A ≃ B) {x y : A}
                → (–> e x ≡ –> e y → x ≡ y)
    equiv-inj e {x} {y} p = ! (<–-inv-l e x) ∙ ap (<– e) p ∙ <–-inv-l e y

  module _ {a b}{A : ★_ a}{B : ★_ b}
           {f : A → B}(g : B → A)
           (f-g : (y : B) → f (g y) ≡ y)
           (g-f : (x : A) → g (f x) ≡ x) where
    is-equiv : Is-equiv f
    is-equiv = record { linv = g ; is-linv = g-f ; rinv = g ; is-rinv = f-g }

  module _ {a b}{A : ★_ a}{B : ★_ b}
           (f : A → B)(g : B → A)
           (f-g : (y : B) → f (g y) ≡ y)
           (g-f : (x : A) → g (f x) ≡ x) where
    equiv : A ≃ B
    equiv = f , is-equiv g f-g g-f

  module _ {ℓ} where
    ≃-refl : Reflexive (_≃_ {ℓ})
    ≃-refl = _ , idᴱ

    ≃-sym : Symmetric (_≃_ {ℓ})
    ≃-sym (_ , fᴱ) = _ , inv-is-equiv fᴱ

    ≃-trans : Transitive (_≃_ {ℓ})
    ≃-trans (_ , p) (_ , q) = _ , q ∘ᴱ p

    ≃-! = ≃-sym
    _≃-∙_ = ≃-trans

  module _ {a}{A : ★_ a} where
    Paths : ★_ a
    Paths = Σ A λ x → Σ A λ y → x ≡ y

    id-path : A → Paths
    id-path x = x , x , idp

    fst-rinv-id-path : ∀ p → id-path (fst p) ≡ p
    fst-rinv-id-path (x , y , p) = snd= (pair= p (J (λ {y} p → tr (_≡_ x) p idp ≡ p) idp p))

    id-path-is-equiv : Is-equiv id-path
    id-path-is-equiv = record { linv = fst
                              ; is-linv = λ x → idp
                              ; rinv = fst
                              ; is-rinv = fst-rinv-id-path }

    ≃-Paths : A ≃ Paths
    ≃-Paths = id-path , id-path-is-equiv

  module _ {a b}{A : ★_ a}{B : ★_ b}(f : A → B) where
    hfiber : (y : B) → ★_(a ⊔ b)
    hfiber y = Σ A λ x → f x ≡ y

    Is-equiv-alt : ★_(a ⊔ b)
    Is-equiv-alt = (y : B) → Is-contr (hfiber y)

  module Is-contr-to-Is-equiv {a}{A : ★_ a}(A-contr : Is-contr A) where
    const-is-equiv : Is-equiv (λ (_ : 𝟙) → fst A-contr)
    const-is-equiv = record { linv = _ ; is-linv = λ _ → idp ; rinv = _ ; is-rinv = snd A-contr }
    𝟙≃ : 𝟙 ≃ A
    𝟙≃ = _ , const-is-equiv
  module Is-equiv-to-Is-contr {a}{A : ★_ a}(f : 𝟙 → A)(f-is-equiv : Is-equiv f) where
    open Is-equiv f-is-equiv
    A-contr : Is-contr A
    A-contr = f _ , is-rinv

  module _ {a}{A : ★_ a}{b}{B : ★_ b} where
    iso-to-equiv : (A ↔ B) → (A ≃ B)
    iso-to-equiv iso = to iso , record { linv = from iso ; is-linv = Inverse.left-inverse-of iso
                                       ; rinv = from iso ; is-rinv = Inverse.right-inverse-of iso }

    equiv-to-iso : (A ≃ B) → (A ↔ B)
    equiv-to-iso (f , f-is-equiv) = inverses f (fᴱ.linv ∘ f ∘ fᴱ.rinv)
                                             (λ x → ap fᴱ.linv (fᴱ.is-rinv (f x)) ∙ fᴱ.is-linv x)
                                             (λ x → ap f (fᴱ.is-linv (fᴱ.rinv x)) ∙ fᴱ.is-rinv x)
      where module fᴱ = Is-equiv f-is-equiv

    {-
    iso-to-equiv-to-iso : (iso : A ↔ B) → equiv-to-iso (iso-to-equiv iso) ≡ iso
    iso-to-equiv-to-iso iso = {!!}
      where module Iso = Inverse iso

    iso-to-equiv-is-equiv : Is-equiv iso-to-equiv
    iso-to-equiv-is-equiv = record { linv = equiv-to-iso ; is-linv = {!!} ; rinv = {!!} ; is-rinv = {!!} }
    -}
open Equivalences

module _ {ℓ}{A : ★_ ℓ} where
    coe!-inv-r : ∀ {B}(p : A ≡ B) y → coe p (coe! p y) ≡ y
    coe!-inv-r idp y = idp

    coe!-inv-l : ∀ {B}(p : A ≡ B) x → coe! p (coe p x) ≡ x
    coe!-inv-l idp x = idp

    coe-equiv : ∀ {B} → A ≡ B → A ≃ B
    coe-equiv p = equiv (coe p) (coe! p) (coe!-inv-r p) (coe!-inv-l p)

postulate
  UA : ★
module _ {ℓ}{A B : ★_ ℓ}{{_ : UA}} where
  postulate
    ua : (A ≃ B) → (A ≡ B)
    coe-equiv-β : (e : A ≃ B) → coe-equiv (ua e) ≡ e
    ua-η : (p : A ≡ B) → ua (coe-equiv p) ≡ p

  ua-equiv : (A ≃ B) ≃ (A ≡ B)
  ua-equiv = equiv ua coe-equiv ua-η coe-equiv-β

  coe-β : (e : A ≃ B) (a : A) → coe (ua e) a ≡ –> e a
  coe-β e a = ap (λ e → –> e a) (coe-equiv-β e)

module _ {{_ : UA}}{{_ : FunExt}}{a}{A₀ A₁ : ★_ a}{b}{B₀ : A₀ → ★_ b}{B₁ : A₁ → ★_ b} where
    Σ≃ : (A : A₀ ≃ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (–> A x))
         → Σ A₀ B₀ ≡ Σ A₁ B₁
    Σ≃ A B = Σ= (ua A) λ x → B x ∙ ap B₁ (! coe-β A x)

    Π≃ : (A : A₀ ≃ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (–> A x))
         → Π A₀ B₀ ≡ Π A₁ B₁
    Π≃ A B = Π= (ua A) λ x → B x ∙ ap B₁ (! coe-β A x)

module _ {{_ : UA}}{{_ : FunExt}}{A : ★}{B C : A → ★} where
    Σ⊎-split : (Σ A (λ x → B x ⊎ C x)) ≡ (Σ A B ⊎ Σ A C)
    Σ⊎-split = ua (equiv (λ { (x , inl y) → inl (x , y)
                            ; (x , inr y) → inr (x , y) })
                         (λ { (inl (x , y)) → x , inl y
                            ; (inr (x , y)) → x , inr y })
                         (λ { (inl (x , y)) → idp
                            ; (inr (x , y)) → idp })
                         (λ { (x , inl y) → idp
                            ; (x , inr y) → idp }))

module _ {{_ : UA}}{{_ : FunExt}}{A B : ★}{C : A → ★}{D : B → ★} where
    dist-⊎-Σ-equiv : (Σ (A ⊎ B) [inl: C ,inr: D ]) ≃ (Σ A C ⊎ Σ B D)
    dist-⊎-Σ-equiv = equiv (λ { (inl x , y) → inl (x , y)
                              ; (inr x , y) → inr (x , y) })
                           [inl: (λ x → inl (fst x) , snd x)
                           ,inr: (λ x → inr (fst x) , snd x) ]
                           [inl: (λ x → idp) ,inr: (λ x → idp) ]
                           (λ { (inl x , y) → idp
                              ; (inr x , y) → idp })

    dist-⊎-Σ : (Σ (A ⊎ B) [inl: C ,inr: D ]) ≡ (Σ A C ⊎ Σ B D)
    dist-⊎-Σ = ua dist-⊎-Σ-equiv

    dist-×-Π-equiv : (Π (A ⊎ B) [inl: C ,inr: D ]) ≃ (Π A C × Π B D)
    dist-×-Π-equiv = equiv (λ f → f ∘ inl , f ∘ inr) (λ fg → [inl: fst fg ,inr: snd fg ])
                           (λ _ → idp) (λ _ → λ= [inl: (λ _ → idp) ,inr: (λ _ → idp) ])

    dist-×-Π : (Π (A ⊎ B) [inl: C ,inr: D ]) ≡ (Π A C × Π B D)
    dist-×-Π = ua dist-×-Π-equiv

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

    𝟙×-fst : {{_ : UA}} → (A × 𝟙) ≡ A
    𝟙×-fst = ×-comm ∙ 𝟙×-snd

module _ {A : ★}{B : A → ★}{C : Σ A B → ★} where
    -- AC: Dependent axiom of choice
    -- In Type Theory it happens to be neither an axiom nor to be choosing anything.
    ΠΣ-comm-equiv : (∀ (x : A) → ∃ λ (y : B x) → C (x , y)) ≃ (∃ λ (f : Π A B) → ∀ (x : A) → C (x , f x))
    ΠΣ-comm-equiv = equiv (λ H → fst ∘ H , snd ∘ H) (λ H → < fst H , snd H >) (λ H → idp) (λ H → idp)

    ΠΣ-comm : {{_ : UA}}
            → (∀ (x : A) → ∃ λ (y : B x) → C (x , y)) ≡ (∃ λ (f : Π A B) → ∀ (x : A) → C (x , f x))
    ΠΣ-comm = ua ΠΣ-comm-equiv
-- -}
-- -}
-- -}
-- -}
