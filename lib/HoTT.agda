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
open ≡ using (_≡_; ap; coe; coe!; !_; _∙_; J; ap↓; PathOver; tr)
       renaming (refl to idp; _≗_ to _∼_; cong₂ to ap₂; J-orig to J')

import Function.Inverse.NP as Inv
open Inv using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)

idp_ : {A : ★₀}(x : A) → x ≡ x
idp_ _ = idp

module _ {A : ★₀} where
  refl-∙ : ∀ {x y : A} (p : x ≡ y) → idp_ x ∙ p ≡ p
  refl-∙ _ = idp

  ∙-refl : ∀ {x y : A} (p : x ≡ y) → p ∙ idp_ y ≡ p
  ∙-refl = J' (λ (x y : A) (p : x ≡ y) → (p ∙ idp_ y) ≡ p) (λ x → idp)

  hom-!-∙ : ∀ {x y z : A} (p : x ≡ y)(q : y ≡ z) → !(p ∙ q) ≡ ! q ∙ ! p
  hom-!-∙ p q = J' (λ x y p → ∀ z → (q : y ≡ z) → !(p ∙ q) ≡ ! q ∙ ! p) (λ x z q → ! ∙-refl (! q)) p _ q

  !-inv : ∀ {x y : A} (p : x ≡ y) → ! (! p) ≡ p
  !-inv = J' (λ x y p → ! (! p) ≡ p) (λ x → idp)

  !-∙ : ∀ {x y : A} (p : x ≡ y) → ! p ∙ p ≡ idp_ y
  !-∙ = J' (λ x y p → (! p ∙ p) ≡ idp_ y) (λ x → idp)

  ∙-! : ∀ {x y : A} (p : x ≡ y) → p ∙ ! p ≡ idp_ x
  ∙-! = J' (λ x y p → (p ∙ ! p) ≡ idp_ x) (λ x → idp)

  !p∙p = !-∙
  p∙!p = ∙-!

  ∙-assoc : ∀ {x y : A} (p : x ≡ y) {z : A} (q : y ≡ z) {t : A} (r : z ≡ t) → p ∙ q ∙ r ≡ (p ∙ q) ∙ r
  ∙-assoc = J' (λ x y p → ∀ {z} (q : y ≡ z) {t} (r : z ≡ t) → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r)
               (λ x q r → idp)

  ==-refl-∙ :  {x y : A} (p : x ≡ y) {q : x ≡ x} → q ≡ idp_ x → q ∙ p ≡ p
  ==-refl-∙ p = ap (flip _∙_ p)

  ∙-==-refl :  {x y : A} (p : x ≡ y) {q : y ≡ y} → q ≡ idp_ y → p ∙ q ≡ p
  ∙-==-refl p qr = ap (_∙_ p) qr ∙ ∙-refl p

  ∙-∙-==-refl :  {x y z : A} (p : x ≡ y) (q : y ≡ z) {r : z ≡ z} → r ≡ idp_ z → p ∙ q ∙ r ≡ p ∙ q
  ∙-∙-==-refl p q rr = ∙-assoc p q _ ∙ ∙-==-refl (p ∙ q) rr

  !p∙p∙q : {x y z : A} (p : x ≡ y) (q : y ≡ z) → ! p ∙ p ∙ q ≡ q
  !p∙p∙q p q = ∙-assoc (! p) p q ∙ ==-refl-∙ q (!-∙ p)

  p∙!p∙q : {x y z : A} (p : y ≡ x) (q : y ≡ z) → p ∙ ! p ∙ q ≡ q
  p∙!p∙q p q = ∙-assoc p _ q ∙ ==-refl-∙ q (∙-! p)

  p∙!q∙q : {x y z : A} (p : x ≡ y) (q : z ≡ y) → p ∙ ! q ∙ q ≡ p
  p∙!q∙q p q = ∙-==-refl p (!-∙ q)

  p∙q∙!q : {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ∙ q ∙ ! q ≡ p
  p∙q∙!q p q = ∙-==-refl p (∙-! q)

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

module _ {a b c}{A : ★_ a}{B : A → ★_ b}{x₀ : A}{y₀ : B x₀}{C : ★_ c}
         (f : (x : A) (y : B x) → C) where
    ap₂↓ : {x₁ : A}(x= : x₀ ≡ x₁)
           {y₁ : B x₁}(y= : y₀ ≡ y₁ [ B ↓ x= ])
         → f x₀ y₀ ≡ f x₁ y₁
    ap₂↓ idp = ap (f x₀)
    {- Or with J
    ap₂↓ x= = J (λ x₁' x=' → {y₁ : B x₁'}(y= : y₀ ≡ y₁ [ _ ↓ x=' ])
                          → f x₀ y₀ ≡ f x₁' y₁)
                (λ y= → ap (f x₀) y=) x=
    -- -}

    apd₂ : {x₁ : A}(x= : x₀ ≡ x₁)
           {y₁ : B x₁}(y= : tr B x= y₀ ≡ y₁)
         → f x₀ y₀ ≡ f x₁ y₁
    -- apd₂ idp = ap (f x₀)
    -- {- Or with J
    apd₂ x= = J (λ x₁' x=' → {y₁ : B x₁'}(y= : tr B x=' y₀ ≡ y₁) → f x₀ y₀ ≡ f x₁' y₁)
                (λ y= → ap (f x₀) y=) x=
    -- -}

module _ {a b c d}{A : ★_ a}{B : A → ★_ b}{C : ★_ c}{x₀ : A}{y₀ : B x₀ → C}{D : ★_ d}
         {{_ : FunExt}}
         (f : (x : A) (y : B x → C) → D) where
    apd₂⁻ : {x₁ : A}(x= : x₀ ≡ x₁)
            {y₁ : B x₁ → C}(y= : ∀ x → y₀ x ≡ y₁ (tr B x= x))
          → f x₀ y₀ ≡ f x₁ y₁
    apd₂⁻ idp y= = ap (f x₀) (λ= y=)

module _ {a b}{A₀ : ★_ a}{B₀ : A₀ → ★_ b}{{_ : FunExt}} where
    Σ= : {A₁ : ★_ a}(A= : A₀ ≡ A₁)
         {B₁ : A₁ → ★_ b}(B= : (x : A₀) → B₀ x ≡ B₁ (coe A= x))
       → Σ A₀ B₀ ≡ Σ A₁ B₁
    Σ= idp B= = Σ=′ _ B=

    Π= : ∀ {A₁ : ★_ a}(A= : A₀ ≡ A₁)
           {B₁ : A₁ → ★_ b}(B= : (x : A₀) → B₀ x ≡ B₁ (coe A= x))
         → Π A₀ B₀ ≡ Π A₁ B₁
    Π= idp B= = Π=′ _ B=

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

  module _ {a}(A : ★_ a) where
    Paths : ★_ a
    Paths = Σ A λ x → Σ A λ y → x ≡ y

  module _ {a}{A : ★_ a} where
    id-path : A → Paths A
    id-path x = x , x , idp

    fst-rinv-id-path : ∀ p → id-path (fst p) ≡ p
    fst-rinv-id-path (x , y , p) = snd= (pair= p (J (λ y p → tr (_≡_ x) p idp ≡ p) idp p))

    id-path-is-equiv : Is-equiv id-path
    id-path-is-equiv = record { linv = fst
                              ; is-linv = λ x → idp
                              ; rinv = fst
                              ; is-rinv = fst-rinv-id-path }

    ≃-Paths : A ≃ Paths A
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

data T-level : ★₀ where
  ⟨-2⟩ : T-level
  ⟨S_⟩ : (n : T-level) → T-level

⟨-1⟩ ⟨0⟩ : T-level
⟨-1⟩ = ⟨S ⟨-2⟩ ⟩
⟨0⟩  = ⟨S ⟨-1⟩ ⟩
⟨1⟩  = ⟨S ⟨0⟩  ⟩
⟨2⟩  = ⟨S ⟨1⟩  ⟩

ℕ₋₂ = T-level

is-contr : ★₀ → ★₀
is-contr A = Σ _ λ(x : A) → (y : A) → x ≡ y

has-level : T-level → ★₀ → ★₀
has-level ⟨-2⟩   A = is-contr A
has-level ⟨S n ⟩ A = (x y : A) → has-level n (x ≡ y)

is-prop : ★₀ → ★₀
is-prop A = has-level ⟨-1⟩ A

is-set : ★₀ → ★₀
is-set A = has-level ⟨0⟩ A

has-all-paths : ★₀ → ★₀
has-all-paths A = (x y : A) → x ≡ y

module _ {A : ★₀} where
    prop-has-all-paths : is-prop A → has-all-paths A
    prop-has-all-paths A-prop x y = fst (A-prop x y)

    all-paths-is-prop : has-all-paths A → is-prop A
    all-paths-is-prop c x y = c x y , canon-path
      where
      lemma : {x y : A} (p : x ≡ y) → c x y ≡ p ∙ c y y
      lemma = J' (λ x y p → c x y ≡ p ∙ c y y) (λ x → idp)

      canon-path : {x y : A} (p : x ≡ y) → c x y ≡ p
      canon-path = J' (λ x y p → c x y ≡ p)
                      (λ x → lemma (! c x x) ∙ !-∙ (c x x))

is-set' : ★₀ → ★₀
is-set' A = {x y : A} → has-all-paths (x ≡ y)

module _ {ℓ}{A : ★_ ℓ} where
    coe!-inv-r : ∀ {B}(p : A ≡ B) y → coe p (coe! p y) ≡ y
    coe!-inv-r idp y = idp

    coe!-inv-l : ∀ {B}(p : A ≡ B) x → coe! p (coe p x) ≡ x
    coe!-inv-l idp x = idp

    coe-equiv : ∀ {B} → A ≡ B → A ≃ B
    coe-equiv p = equiv (coe p) (coe! p) (coe!-inv-r p) (coe!-inv-l p)

    coe∘coe : ∀ {B C}(p : B ≡ C)(q : A ≡ B)(m : A) → coe p (coe q m) ≡ coe (q ∙ p) m
    coe∘coe p idp m = idp

    coe-same : ∀ {B}{p q : A ≡ B}(e : p ≡ q)(x : A) → coe p x ≡ coe q x
    coe-same idp x = idp

    coe-inj : ∀ {B}{x y : A}(p : A ≡ B) → coe p x ≡ coe p y → x ≡ y
    coe-inj idp = id

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
    Σ≃ : (A≃ : A₀ ≃ A₁)(B= : (x : A₀) → B₀ x ≡ B₁ (–> A≃ x))
         → Σ A₀ B₀ ≡ Σ A₁ B₁
    Σ≃ A≃ B= = Σ= (ua A≃) λ x → B= x ∙ ap B₁ (! coe-β A≃ x)

    Π≃ : (A : A₀ ≃ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (–> A x))
         → Π A₀ B₀ ≡ Π A₁ B₁
    Π≃ A B = Π= (ua A) λ x → B x ∙ ap B₁ (! coe-β A x)

module _ {{_ : UA}}{{_ : FunExt}}{a}{A₀ A₁ : ★_ a}{b}{B : A₀ → ★_ b} where
    Σ-first : (A : A₀ ≃ A₁) → Σ A₀ B ≡ Σ A₁ (B ∘ <– A)
    Σ-first A = Σ≃ A (λ x → ap B (! <–-inv-l A x))

    Π-first : (A : A₀ ≃ A₁) → Π A₀ B ≡ Π A₁ (B ∘ <– A)
    Π-first A = Π≃ A (λ x → ap B (! <–-inv-l A x))
-- -}
-- -}
-- -}
