{-# OPTIONS --without-K #-}
module HoTT where

open import Type
open import Level.NP
open import Function.NP
open import Function.Extensionality
open import Data.Zero using (𝟘; 𝟘-elim)
open import Data.One using (𝟙)
open import Data.Product.NP
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_])
open import Relation.Nullary.NP
open import Relation.Binary using (Reflexive; Symmetric; Transitive)
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; ap; coe; coe!; !_; _∙_; J; ap↓; PathOver; tr; ap₂)
       renaming (refl to idp; _≗_ to _∼_; J-orig to J')
open ≡.≡-Reasoning

import Function.Inverse.NP as Inv
open Inv using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)

module _ {a} {A : ★_ a} where
  idp_ : (x : A) → x ≡ x
  idp_ _ = idp

  refl-∙ : ∀ {x y : A} (p : x ≡ y) → idp_ x ∙ p ≡ p
  refl-∙ _ = idp

  ∙-refl : ∀ {x y : A} (p : x ≡ y) → p ∙ idp_ y ≡ p
  ∙-refl = J' (λ (x y : A) (p : x ≡ y) → (p ∙ idp_ y) ≡ p) (λ x → idp)

  -- could be derived in any groupoid
  hom-!-∙ : ∀ {x y z : A} (p : x ≡ y)(q : y ≡ z) → !(p ∙ q) ≡ ! q ∙ ! p
  hom-!-∙ p q = J' (λ x y p → ∀ z → (q : y ≡ z) → !(p ∙ q) ≡ ! q ∙ ! p) (λ x z q → ! ∙-refl (! q)) p _ q

  module _ {x y : A} where

    ∙-assoc : (p : x ≡ y) {z : A} (q : y ≡ z) {t : A} (r : z ≡ t) → p ∙ q ∙ r ≡ (p ∙ q) ∙ r
    ∙-assoc = J' (λ x y p → ∀ {z} (q : y ≡ z) {t} (r : z ≡ t) → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r)
                 (λ x q r → idp)

    module _ (p : x ≡ y) where
      -- ! is a left-inverse for _∙_
      !-∙ : ! p ∙ p ≡ idp_ y
      !-∙ = J' (λ x y p → (! p ∙ p) ≡ idp_ y) (λ x → idp) p

      -- ! is a right-inverse for _∙_
      ∙-! : p ∙ ! p ≡ idp_ x
      ∙-! = J' (λ x y p → (p ∙ ! p) ≡ idp_ x) (λ x → idp) p

      -- ! is involutive
      !-involutive : ! (! p) ≡ p
      !-involutive = J' (λ x y p → ! (! p) ≡ p) (λ x → idp) p

      !p∙p = !-∙
      p∙!p = ∙-!

      ==-refl-∙ : {q : x ≡ x} → q ≡ idp_ x → q ∙ p ≡ p
      ==-refl-∙ = ap (flip _∙_ p)

      ∙-==-refl : {q : y ≡ y} → q ≡ idp_ y → p ∙ q ≡ p
      ∙-==-refl qr = ap (_∙_ p) qr ∙ ∙-refl p

  module _ {x y : A} where
    module _ (p : x ≡ x)(q : x ≡ y)(e : p ∙ q ≡ q) where
      unique-idp-left : p ≡ idp
      unique-idp-left
        = p              ≡⟨ ! ∙-refl p ⟩
          p ∙ idp        ≡⟨ ap (_∙_ p) (! ∙-! q) ⟩
          p ∙ (q ∙ ! q)  ≡⟨ ∙-assoc p q (! q) ⟩
          (p ∙ q) ∙ ! q  ≡⟨ ap (flip _∙_ (! q)) e ⟩
          q ∙ ! q        ≡⟨ ∙-! q ⟩
          idp            ∎

  module _ {x y z : A}{p₀ p₁ : x ≡ y}{q₀ q₁ : y ≡ z}(p : p₀ ≡ p₁)(q : q₀ ≡ q₁) where
      ∙= : p₀ ∙ q₀ ≡ p₁ ∙ q₁
      ∙= = ap (flip _∙_ q₀) p ∙ ap (_∙_ p₁) q

  module _ {x y z : A} where
    module _ (p : x ≡ y)(q : y ≡ z) where
      ∙-∙-==-refl : {r : z ≡ z} → r ≡ idp_ z → p ∙ q ∙ r ≡ p ∙ q
      ∙-∙-==-refl rr = ∙-assoc p q _ ∙ ∙-==-refl (p ∙ q) rr

      !p∙p∙q : ! p ∙ p ∙ q ≡ q
      !p∙p∙q = ∙-assoc (! p) p q ∙ ==-refl-∙ q (!-∙ p)

    p∙!p∙q : (p : y ≡ x) (q : y ≡ z) → p ∙ ! p ∙ q ≡ q
    p∙!p∙q p q = ∙-assoc p _ q ∙ ==-refl-∙ q (∙-! p)

    p∙!q∙q : (p : x ≡ y) (q : z ≡ y) → p ∙ ! q ∙ q ≡ p
    p∙!q∙q p q = ∙-==-refl p (!-∙ q)

    p∙q∙!q : (p : x ≡ y) (q : y ≡ z) → p ∙ q ∙ ! q ≡ p
    p∙q∙!q p q = ∙-==-refl p (∙-! q)

    ∙-cancel : {p q : x ≡ y}(r : y ≡ z) → p ∙ r ≡ q ∙ r → p ≡ q
    ∙-cancel {p = p} {q} r e
      = p               ≡⟨ ! p∙q∙!q p r ⟩
         p ∙ r  ∙ ! r   ≡⟨ ∙-assoc p r (! r) ⟩
        (p ∙ r) ∙ ! r   ≡⟨ ∙= e idp ⟩
        (q ∙ r) ∙ ! r   ≡⟨ ! ∙-assoc q r (! r) ⟩
        q ∙ (r  ∙ ! r)  ≡⟨ p∙q∙!q q r ⟩
        q               ∎

    ∙-cancel′ : (p : x ≡ y){q r : y ≡ z} → p ∙ q ≡ p ∙ r → q ≡ r
    ∙-cancel′ p {q} {r} e
      = q             ≡⟨ ! !p∙p∙q p q ⟩
        ! p ∙ p ∙ q   ≡⟨ ap (_∙_ (! p)) e  ⟩
        ! p ∙ p ∙ r   ≡⟨ !p∙p∙q p r ⟩
        r             ∎

!-ap : ∀ {a b}{A : Set a}{B : Set b}(f : A → B){x y}(p : x ≡ y)
       → ! (ap f p) ≡ ap f (! p)
!-ap f idp = idp

ap-id : ∀ {a}{A : Set a}{x y : A}(p : x ≡ y) → ap id p ≡ p
ap-id idp = idp

ap-∘ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}(f : B → C)(g : A → B){x y}(p : x ≡ y)
       → ap (f ∘ g) p ≡ ap f (ap g p)
ap-∘ f g idp = idp

module _ {a b}{A : Set a}{B : Set b}{f g : A → B}(H : ∀ x → f x ≡ g x) where
  ap-nat : ∀ {x y}(q : x ≡ y) → ap f q ∙ H _ ≡ H _ ∙ ap g q
  ap-nat idp = ! ∙-refl _

module _ {a}{A : Set a}{f : A → A}(H : ∀ x → f x ≡ x) where
  ap-nat-id : ∀ x → ap f (H x) ≡ H (f x)
  ap-nat-id x = ∙-cancel (H x) (ap-nat H (H x) ∙ ap (_∙_ (H (f x))) (ap-id (H x)))

tr-∘ : ∀ {a b p}{A : Set a}{B : Set b}(P : B → Set p)(f : A → B){x y}(p : x ≡ y)
  → tr (P ∘ f) p ≡ tr P (ap f p)
tr-∘ P f idp = idp

module _ {a}{A : ★_ a} where
    tr-∙′ : ∀ {ℓ}(P : A → ★_ ℓ) {x y z} (p : x ≡ y) (q : y ≡ z) →
             tr P (p ∙ q) ∼ tr P q ∘ tr P p
    tr-∙′ P idp _ _ = idp

    tr-∙ : ∀ {ℓ}(P : A → ★_ ℓ) {x y z} (p : x ≡ y) (q : y ≡ z) (pq : x ≡ z) →
             pq ≡ p ∙ q →
             tr P pq ∼ tr P q ∘ tr P p
    tr-∙ P p q ._ idp = tr-∙′ P p q

module _ {k} {K : ★_ k} {a} {A : ★_ a} {x y : A} (p : x ≡ y) where
    tr-const : tr (const K) p ≡ id
    tr-const = J (λ _ p₁ → tr (const K) p₁ ≡ id) idp p

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

module _ {a}{A : ★_ a} where
  tr-r≡ : {x y z : A}(p : y ≡ z)(q : x ≡ y) → tr (λ v → x ≡ v) p q ≡ q ∙ p
  tr-r≡ idp q = ! ∙-refl q

  tr-l≡ : {x y z : A}(p : x ≡ y)(q : x ≡ z) → tr (λ v → v ≡ z) p q ≡ ! p ∙ q
  tr-l≡ idp q = idp

module _ {A : ★}(f g : A → ★){x y : A}(p : x ≡ y)(h : f x → g x) where
    tr-→ : tr (λ x → f x → g x) p h ≡ (λ x → tr g p (h (tr f (! p) x)))
    tr-→ = J' (λ x y p → (h : f x → g x) → tr (λ x → f x → g x) p h ≡ (λ x → tr g p (h (tr f (! p) x))))
             (λ _ _ → idp) p h

module _ {a}{b}{A : ★_ a}{B : ★_ b} where
    pair×= : ∀ {x x' : A}(p : x ≡ x')
               {y y' : B}(q : y ≡ y')
             → (x , y) ≡ (x' , y')
    pair×= idp q = snd= q

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

module Equivalences where

  module _ {a b}{A : ★_ a}{B : ★_ b} where
    _LeftInverseOf_ : (B → A) → (A → B) → ★_ a
    linv LeftInverseOf f = ∀ x → linv (f x) ≡ x

    _RightInverseOf_ : (B → A) → (A → B) → ★_ b
    rinv RightInverseOf f = ∀ x → f (rinv x) ≡ x

    record Linv (f : A → B) : ★_(a ⊔ b) where
      field
        linv    : B → A
        is-linv : ∀ x → linv (f x) ≡ x

      injective : ∀ {x y} → f x ≡ f y → x ≡ y
      injective p = ! is-linv _ ∙ ap linv p ∙ is-linv _

    record Rinv (f : A → B) : ★_(a ⊔ b) where
      field
        rinv    : B → A
        is-rinv : ∀ x → f (rinv x) ≡ x

      surjective : ∀ y → ∃ λ x → f x ≡ y
      surjective y = rinv y , is-rinv y

    record Biinv (f : A → B) : ★_(a ⊔ b) where
      field
        has-linv : Linv f
        has-rinv : Rinv f

      open Linv has-linv public
      open Rinv has-rinv public

    module _ {f : A → B}
             (g : B → A)(g-f : (x : A) → g (f x) ≡ x)
             (h : B → A)(f-h : (y : B) → f (h y) ≡ y) where
      biinv : Biinv f
      biinv = record { has-linv = record { linv = g ; is-linv = g-f }
                     ; has-rinv = record { rinv = h ; is-rinv = f-h } }

    record Qinv (f : A → B) : ★_(a ⊔ b) where
      field
        inv : B → A
        inv-is-linv : ∀ x → inv (f x) ≡ x
        inv-is-rinv : ∀ x → f (inv x) ≡ x

      has-biinv : Biinv f
      has-biinv = record { has-linv = record { linv = inv
                                             ; is-linv = inv-is-linv }
                         ; has-rinv = record { rinv = inv
                                             ; is-rinv = inv-is-rinv } }

      open Biinv has-biinv public

    HAE : {f : A → B} → Qinv f → ★_(a ⊔ b)
    HAE {f} f-qinv = ∀ x → ap f (F.inv-is-linv x) ≡ F.inv-is-rinv (f x)
      where module F = Qinv f-qinv

    record Is-equiv (f : A → B) : ★_(a ⊔ b) where
      field
        has-qinv : Qinv f
        is-hae   : HAE has-qinv
      open Qinv has-qinv public

    module _ {f : A → B}(g : B → A)
             (f-g : (y : B) → f (g y) ≡ y)
             (g-f : (x : A) → g (f x) ≡ x) where
      qinv : Qinv f
      qinv = record
            { inv = g
            ; inv-is-linv = g-f
            ; inv-is-rinv = f-g }

    module _ {f : A → B}(g : B → A)
             (f-g : (y : B) → f (g y) ≡ y)
             (g-f : (x : A) → g (f x) ≡ x) where
      f-g' : (x : B) → f (g x) ≡ x
      f-g' x = ! ap (f ∘ g) (f-g x) ∙ ap f (g-f (g x)) ∙ f-g x
      -- g-f' x = ap g {!f-g ?!} ∙ {!!}

      hae : HAE (qinv g f-g' g-f)
      hae a = ∙-cancel′ (ap (f ∘ g) (f-g (f a)))
        (ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a) ≡⟨ ∙= (ap-nat-id f-g (f a)) (! ap-id (ap f (g-f a))) ⟩
         f-g (f (g (f a))) ∙ ap id (ap f (g-f a))  ≡⟨ ! ap-nat f-g {f (g (f a))} {f a} (ap f (g-f a)) ⟩
         ap (f ∘ g) (ap f (g-f a)) ∙ f-g (f a)    ≡⟨ ap (flip _∙_ (f-g (f a))) (! ap-∘ (f ∘ g) f (g-f a)
                                                                               ∙ ap-∘ f (g ∘ f) (g-f a))  ⟩
         ap f (ap (λ z → g (f z)) (g-f a)) ∙ f-g (f a) ≡⟨ ap (flip _∙_ (f-g (f a))) (ap (ap f) (ap-nat-id g-f a)) ⟩
         ap f (g-f (g (f a))) ∙ f-g (f a)      ≡⟨ ! p∙!p∙q (ap (f ∘ g) (f-g (f a))) (ap f (g-f (g (f a))) ∙ f-g (f a)) ⟩
         ap (f ∘ g) (f-g (f a)) ∙ ! ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f (g (f a))) ∙ f-g (f a)    ∎
        )

      is-equiv : Is-equiv f
      is-equiv = record
        { has-qinv = qinv g f-g' g-f
        ; is-hae   = hae }

  module Biinv-inv {a b}{A : ★_ a}{B : ★_ b}{f : A → B}
                   (fᴮ : Biinv f) where
      open Biinv fᴮ
      inv : B → A
      inv = linv ∘ f ∘ rinv

      inv-biinv : Biinv inv
      inv-biinv =
        biinv f (λ x → ap f (is-linv (rinv x)) ∙ is-rinv x)
              f (λ x → ap linv (is-rinv (f x)) ∙ is-linv x)

  module _ {a b}{A : ★_ a}{B : ★_ b}{f : A → B}
           (fᴱ : Is-equiv f) where
      open Is-equiv fᴱ

      inv-is-equiv : Is-equiv inv
      inv-is-equiv = is-equiv f is-linv is-rinv

  module _ {a b} where
    infix 4 _≃_
    _≃_ : ★_ a → ★_ b → ★_(a ⊔ b)
    A ≃ B = Σ (A → B) Is-equiv

  module _ {a b}{A : ★_ a}{B : ★_ b}
           (f : A → B)(g : B → A)
           (f-g : (y : B) → f (g y) ≡ y)
           (g-f : (x : A) → g (f x) ≡ x) where
    equiv : A ≃ B
    equiv = f , is-equiv g f-g g-f

  module _ {a}{A : ★_ a}
           (f : A → A)(f-inv : f LeftInverseOf f) where
      self-inv-is-equiv : Is-equiv f
      self-inv-is-equiv = is-equiv f f-inv f-inv

      self-inv-equiv : A ≃ A
      self-inv-equiv = f , self-inv-is-equiv

      self-inv-biinv : Biinv f
      self-inv-biinv = biinv f f-inv f f-inv

  module _ {a}{A : ★_ a} where
    idᴱ : Is-equiv {A = A} id
    idᴱ = self-inv-is-equiv _ λ _ → idp

    idᴮ : Biinv {A = A} id
    idᴮ = self-inv-biinv _ λ _ → idp

  module _ {a b c}{A : ★_ a}{B : ★_ b}{C : ★_ c}{g : B → C}{f : A → B} where
    _∘ᴱ_ : Is-equiv g → Is-equiv f → Is-equiv (g ∘ f)
    gᴱ ∘ᴱ fᴱ = is-equiv (F.inv ∘ G.inv)
                        (λ x → ap g (F.inv-is-rinv _) ∙ G.inv-is-rinv _)
                        (λ x → ap F.inv (G.inv-is-linv _) ∙ F.inv-is-linv _)
      where
        module G = Is-equiv gᴱ
        module F = Is-equiv fᴱ

    _∘ᴮ_ : Biinv g → Biinv f → Biinv (g ∘ f)
    gᴮ ∘ᴮ fᴮ =
      biinv (F.linv ∘ G.linv)
            (λ x → ap F.linv (G.is-linv (f x)) ∙ F.is-linv x)
            (F.rinv ∘ G.rinv)
            (λ x → ap g (F.is-rinv _) ∙ G.is-rinv x)
      where
        module G = Biinv gᴮ
        module F = Biinv fᴮ

  module Equiv {a b}{A : ★_ a}{B : ★_ b}(e : A ≃ B) where
    ·→ : A → B
    ·→ = fst e

    open Is-equiv (snd e) public
      renaming (linv to ·←; rinv to ·←′; is-linv to ·←-inv-l; is-rinv to ·←-inv-r)

    -- Equivalences are "injective"
    equiv-inj : {x y : A} → (·→ x ≡ ·→ y → x ≡ y)
    equiv-inj p = ! ·←-inv-l _ ∙ ap ·← p ∙ ·←-inv-l _

    –> = ·→
    <– = ·←
    <–' = ·←′

    <–-inv-l = ·←-inv-l
    <–-inv-r = ·←-inv-r

  open Equiv public

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
    id-path-is-equiv = is-equiv fst fst-rinv-id-path (λ x → idp)

    ≃-Paths : A ≃ Paths A
    ≃-Paths = id-path , id-path-is-equiv

  module _ {a b}{A : ★_ a}{B : ★_ b}(f : A → B) where
    hfiber : (y : B) → ★_(a ⊔ b)
    hfiber y = Σ A λ x → f x ≡ y

    Is-equiv-alt : ★_(a ⊔ b)
    Is-equiv-alt = (y : B) → Is-contr (hfiber y)

  module Is-contr-to-Is-equiv {a}{A : ★_ a}(A-contr : Is-contr A) where
    const-is-equiv : Is-equiv (λ (_ : 𝟙) → fst A-contr)
    const-is-equiv = is-equiv _ (snd A-contr) (λ _ → idp)
    𝟙≃ : 𝟙 ≃ A
    𝟙≃ = _ , const-is-equiv
  module Is-equiv-to-Is-contr {a}{A : ★_ a}(f : 𝟙 → A)(f-is-equiv : Is-equiv f) where
    open Is-equiv f-is-equiv
    A-contr : Is-contr A
    A-contr = f _ , is-rinv

  module _ {a}{A : ★_ a}{b}{B : ★_ b} where
    iso-to-equiv : (A ↔ B) → (A ≃ B)
    iso-to-equiv iso = to iso , is-equiv (from iso) (Inverse.right-inverse-of iso) (Inverse.left-inverse-of iso)

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

module _ {a} where
    private
      U = ★_ a

    has-level : T-level → U → U
    has-level ⟨-2⟩   A = Is-contr A
    has-level ⟨S n ⟩ A = (x y : A) → has-level n (x ≡ y)

    is-prop : U → U
    is-prop A = has-level ⟨-1⟩ A

    is-set : U → U
    is-set A = has-level ⟨0⟩ A

    has-all-paths : U → U
    has-all-paths A = (x y : A) → x ≡ y

    UIP : U → U
    UIP A = {x y : A} (p q : x ≡ y) → p ≡ q

    private
      UIP-check : {A : U} → UIP A ≡ ({x y : A} → has-all-paths (x ≡ y))
      UIP-check = idp

    module _ {A : U} where
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

      Is-contr→is-prop : Is-contr A → is-prop A
      Is-contr→is-prop (x , p) y z
         = ! p y ∙ p z
         , J' (λ y₁ z₁ q → ! p y₁ ∙ p z₁ ≡ q) (!-∙ ∘ p)

      {-
      has-level-up : ∀ {n} → has-level n A → has-level ⟨S n ⟩ A
      has-level-up {⟨-2⟩} = Is-contr→is-prop
      has-level-up {⟨S n ⟩} π x y p q = {!!}

      Is-contr-is-prop : is-prop (Is-contr A)
      Is-contr-is-prop (x , p) (y , q) = ?

      module _ {{_ : FunExt}} where
        is-prop-is-prop : has-all-paths (has-all-paths A)
        is-prop-is-prop h0 h1 = λ= λ x → λ= λ y → {!!}
      -}

𝟘-is-prop : is-prop 𝟘
𝟘-is-prop () _

𝟘-has-all-paths : has-all-paths 𝟘
𝟘-has-all-paths () _

𝟙-is-contr : Is-contr 𝟙
𝟙-is-contr = _ , λ _ → idp

𝟙-is-prop : is-prop 𝟙
𝟙-is-prop = Is-contr→is-prop 𝟙-is-contr

𝟙-has-all-paths : has-all-paths 𝟙
𝟙-has-all-paths _ _ = idp

module _ {{_ : FunExt}}{a b}{A : ★_ a}{B : A → ★_ b} where
  Π-has-all-paths : (∀ x → has-all-paths (B x)) → has-all-paths (Π A B)
  Π-has-all-paths B-has-all-paths f g
    = λ= λ _ → B-has-all-paths _ _ _

  Π-is-prop : (∀ x → is-prop (B x)) → is-prop (Π A B)
  Π-is-prop B-is-prop = all-paths-is-prop (Π-has-all-paths (prop-has-all-paths ∘ B-is-prop))

module _ {{_ : FunExt}}{a}{A : ★_ a} where
    ¬-has-all-paths : has-all-paths (¬ A)
    ¬-has-all-paths = Π-has-all-paths (λ _ → 𝟘-has-all-paths)

    ¬-is-prop : is-prop (¬ A)
    ¬-is-prop = Π-is-prop (λ _ → 𝟘-is-prop)

module _ {a} (A : ★_ a) where
    has-dec-eq : ★_ a
    has-dec-eq = (x y : A) → Dec (x ≡ y)

module _ {a} {A : ★_ a} (d : has-dec-eq A) where
    private
        Code' : {x y : A} (dxy : Dec (x ≡ y)) (dxx : Dec (x ≡ x)) → x ≡ y → ★_ a
        Code' {x} {y} dxy dxx p = case dxy of λ
          { (no  _) → Lift 𝟘
          ; (yes b) → case dxx of λ
                      { (no   _) → Lift 𝟘
                      ; (yes b') → p ≡ ! b' ∙ b
                      }
          }

        Code : {x y : A} → x ≡ y → ★_ a
        Code {x} {y} p = Code' (d x y) (d x x) p

        encode : {x y : A} → (p : x ≡ y) -> Code p
        encode {x} = J (λ y (p : x ≡ y) → Code p) (elim-Dec (λ d → Code' d d idp) (!_ ∘ !p∙p) (λ x₁ → lift (x₁ idp)) (d x x))

    UIP-dec : UIP A
    UIP-dec {x} idp q with d x x | encode q
    UIP-dec     idp q    | yes a | p' = ! !p∙p a ∙ ! p'
    UIP-dec     idp q    | no  r | _  = 𝟘-elim (r idp)

    dec-eq-is-set : is-set A
    dec-eq-is-set _ _ = all-paths-is-prop UIP-dec

module _ {ℓ}{A : ★_ ℓ} where
    UIP-set : is-set A → UIP A
    UIP-set A-is-set p q = fst (A-is-set _ _ p q)

    UIP→is-set : UIP A → is-set A
    UIP→is-set A-is-set' x y = all-paths-is-prop A-is-set'

    Ω₁-set-to-contr : is-set A → (x : A) → Is-contr (x ≡ x)
    Ω₁-set-to-contr A-is-set x = idp , UIP-set A-is-set idp

    coe!-inv-r : ∀ {B}(p : A ≡ B) y → coe p (coe! p y) ≡ y
    coe!-inv-r idp y = idp

    coe!-inv-l : ∀ {B}(p : A ≡ B) x → coe! p (coe p x) ≡ x
    coe!-inv-l idp x = idp

    coe-equiv : ∀ {B} → A ≡ B → A ≃ B
    coe-equiv p = equiv (coe p) (coe! p) (coe!-inv-r p) (coe!-inv-l p)

    coe∘coe : ∀ {B C}(p : B ≡ C)(q : A ≡ B)(m : A) → coe p (coe q m) ≡ coe (q ∙ p) m
    coe∘coe p idp m = idp

    coe-same : ∀ {B}{p q : A ≡ B}(e : p ≡ q)(x : A) → coe p x ≡ coe q x
    coe-same p x = ap (λ X → coe X x) p

    coe-inj : ∀ {B}{x y : A}(p : A ≡ B) → coe p x ≡ coe p y → x ≡ y
    coe-inj idp = id

    module _ {B : ★_ ℓ}(p : A ≡ B){x y : A} where
        coe-paths-equiv : (x ≡ y) ≡ (coe p x ≡ coe p y)
        coe-paths-equiv = J (λ B (p : A ≡ B) → (x ≡ y) ≡ (coe p x ≡ coe p y)) idp p

postulate
  UA : ★
module _ {ℓ}{A B : ★_ ℓ}{{_ : UA}} where
  postulate
    ua : (A ≃ B) → (A ≡ B)
    coe-equiv-β : (e : A ≃ B) → coe-equiv (ua e) ≡ e
    ua-η : (p : A ≡ B) → ua (coe-equiv p) ≡ p

  ua-equiv : (A ≃ B) ≃ (A ≡ B)
  ua-equiv = equiv ua coe-equiv ua-η coe-equiv-β

  coe-β : (e : A ≃ B) (a : A) → coe (ua e) a ≡ ·→ e a
  coe-β e a = ap (λ e → ·→ e a) (coe-equiv-β e)

  postulate
    coe!-β : (e : A ≃ B) (b : B) → coe! (ua e) b ≡ ·← e b

  module _ (e : A ≃ B){x y : A} where
    ·→-paths-equiv : (x ≡ y) ≡ (·→ e x ≡ ·→ e y)
    ·→-paths-equiv = coe-paths-equiv (ua e) ∙ ap₂ _≡_ (coe-β e x) (coe-β e y)

    –>-paths-equiv = ·→-paths-equiv

-- -}
-- -}
-- -}
-- -}
