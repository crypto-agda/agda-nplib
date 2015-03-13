{-# OPTIONS --without-K #-}
open import Type

open import Level.NP
open import HoTT
open import Function.NP
open import Function.Extensionality

open import Data.Maybe.NP using (Maybe ; just ; nothing ; maybe ; maybe′ ; just-injective; Maybe^)
open import Data.Zero using (𝟘 ; 𝟘-elim)
open import Data.One using (𝟙)
open import Data.Two
open import Data.Fin.NP as Fin using (Fin; suc; zero; [zero:_,suc:_])
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Nat.NP as ℕ using (ℕ ; suc ; zero; _+_)
open import Data.Product.NP renaming (map to map×)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_]; map to map⊎)

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≢_ ; ap; coe; coe!; !_; _∙_; J ; inspect ; [_]; tr; ap₂; apd) renaming (refl to idp; _≗_ to _∼_; J-orig to J')

module Type.Identities where

open Equivalences



module _ {a}{A₀ A₁ : ★_ a}{b}{B₀ B₁ : ★_ b}(A= : A₀ ≡ A₁)(B= : B₀ ≡ B₁) where
    ×= : (A₀ × B₀) ≡ (A₁ × B₁)
    ×= = ap₂ _×_ A= B=

    ⊎= : (A₀ ⊎ B₀) ≡ (A₁ ⊎ B₁)
    ⊎= = ap₂ _⊎_ A= B=

    →= : (A₀ → B₀) ≡ (A₁ → B₁)
    →= = ap₂ -→- A= B=


coe×= : ∀ {a}{A₀ A₁ : ★_ a}{b}{B₀ B₁ : ★_ b}(A= : A₀ ≡ A₁)(B= : B₀ ≡ B₁){x y}
      → coe (×= A= B=) (x , y) ≡ (coe A= x , coe B= y)
coe×= idp idp = idp


module _ {a}{A₀ A₁ : ★_ a}{b}{B₀ B₁ : ★_ b}(A≃ : A₀ ≃ A₁)(B≃ : B₀ ≃ B₁) where
    private
      module A≃ = Equiv A≃
      A→ = A≃.·→
      A← = A≃.·←
      module B≃ = Equiv B≃
      B→ = B≃.·→
      B← = B≃.·←

    {-
    ×≃ : (A₀ × B₀) ≃ (A₁ × B₁)
    ×≃ = equiv (map× A→ B→) (map× A← B←)
               (λ { (x , y) → pair= (A≃.·←-inv-r x) ({!coe-β!} ∙ B≃.·←-inv-r y) })
               (λ { (x , y) → pair= (A≃.·←-inv-l x) {!!} })
    -}

    ⊎≃ : (A₀ ⊎ B₀) ≃ (A₁ ⊎ B₁)
    ⊎≃ = equiv (map⊎ A→ B→) (map⊎ A← B←)
               [inl: (λ x → ap inl (A≃.·←-inv-r x)) ,inr: ap inr ∘ B≃.·←-inv-r ]
               [inl: (λ x → ap inl (A≃.·←-inv-l x)) ,inr: ap inr ∘ B≃.·←-inv-l ]

    →≃ : {{_ : FunExt}} → (A₀ → B₀) ≃ (A₁ → B₁)
    →≃ = equiv (λ f → B→ ∘ f ∘ A←)
               (λ f → B← ∘ f ∘ A→)
               (λ f → λ= (λ x → B≃.·←-inv-r _ ∙ ap f (A≃.·←-inv-r x))) 
               (λ f → λ= (λ x → B≃.·←-inv-l _ ∙ ap f (A≃.·←-inv-l x)))

module _ {{_ : FunExt}}{a}(A : ★_ a){b}{B₀ B₁ : A → ★_ b}(B : (x : A) → B₀ x ≡ B₁ x) where
    Σ=′ : Σ A B₀ ≡ Σ A B₁
    Σ=′ = ap (Σ A) (λ= B)

    Π=′ : Π A B₀ ≡ Π A B₁
    Π=′ = ap (Π A) (λ= B)

module _ {a b}{A₀ : ★_ a}{B₀ : A₀ → ★_ b}{{_ : FunExt}} where
    Σ= : {A₁ : ★_ a}(A= : A₀ ≡ A₁)
         {B₁ : A₁ → ★_ b}(B= : (x : A₀) → B₀ x ≡ B₁ (coe A= x))
       → Σ A₀ B₀ ≡ Σ A₁ B₁
    Σ= = J (λ A₁ A= → {B₁ : A₁ → ★_ b}(B= : (x : A₀) → B₀ x ≡ B₁ (coe A= x))
                    → Σ A₀ B₀ ≡ Σ A₁ B₁) (Σ=′ _)
    -- Σ= idp B= = Σ=′ _ B=

    Π= : ∀ {A₁ : ★_ a}(A= : A₀ ≡ A₁)
           {B₁ : A₁ → ★_ b}(B= : (x : A₀) → B₀ x ≡ B₁ (coe A= x))
         → Π A₀ B₀ ≡ Π A₁ B₁
    Π= idp B= = Π=′ _ B=

module _ {a}(A : ★_ a){b}{B₀ B₁ : A → ★_ b}(B : (x : A) → B₀ x ≡ B₁ x){{_ : FunExt}} where
  !Σ=′ : ! (Σ=′ A B) ≡ Σ=′ A (!_ ∘ B)
  !Σ=′ = !-ap _ (λ= B) ∙ ap (ap (Σ A)) (!-λ= B)

coeΣ=′-aux : ∀{{_ : FunExt}}{a}(A : ★_ a){b}{B₀ B₁ : A → ★_ b}(B : (x : A) → B₀ x ≡ B₁ x){x y}
  → coe (Σ=′ A B) (x , y) ≡ (x , coe (ap (λ f → f x) (λ= B)) y)
coeΣ=′-aux A B with λ= B
coeΣ=′-aux A B | idp = idp

coeΣ=′ : ∀{{_ : FunExt}}{a}(A : ★_ a){b}{B₀ B₁ : A → ★_ b}(B : (x : A) → B₀ x ≡ B₁ x){x y}
  → coe (Σ=′ A B) (x , y) ≡ (x , coe (B x) y)
coeΣ=′ A B = coeΣ=′-aux A B ∙ ap (_,_ _) (coe-same (happly (happly-λ= B) _) _)

coe!Σ=′ : ∀{{_ : FunExt}}{a}(A : ★_ a){b}{B₀ B₁ : A → ★_ b}(B : (x : A) → B₀ x ≡ B₁ x){x y}
  → coe! (Σ=′ A B) (x , y) ≡ (x , coe! (B x) y)
coe!Σ=′ A B {x}{y} = coe-same (!Σ=′ A B) _ ∙ coeΣ=′ A (!_ ∘ B)

module _ {{_ : UA}}{{_ : FunExt}}{a}{A₀ A₁ : ★_ a}{b}{B₀ : A₀ → ★_ b}{B₁ : A₁ → ★_ b} where
    Σ≃ : (A≃ : A₀ ≃ A₁)(B= : (x : A₀) → B₀ x ≡ B₁ (–> A≃ x))
         → Σ A₀ B₀ ≡ Σ A₁ B₁
    Σ≃ A≃ B= = Σ= (ua A≃) λ x → B= x ∙ ap B₁ (! coe-β A≃ x)

    Π≃ : (A : A₀ ≃ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (–> A x))
         → Π A₀ B₀ ≡ Π A₁ B₁
    Π≃ A B = Π= (ua A) λ x → B x ∙ ap B₁ (! coe-β A x)

    {-
module _ {{_ : FunExt}}{a}{A₀ A₁ : ★_ a}{b}{B₀ : A₀ → ★_ b}{B₁ : A₁ → ★_ b}(A : A₀ ≃ A₁)(B : (x : A₁) → B₀ (<– A x) ≃ B₁ x) where
    Π≃' : (Π A₀ B₀) ≃ (Π A₁ B₁)
    Π≃' = equiv (λ f x → –> (B x) (f (<– A x)))
                (λ f x → tr B₀ (<–-inv-l A x) (<– (B (–> A x)) (f (–> A x))))
                (λ f → λ= (λ x → {!apd (<–-inv-l A (<– A x))!}))
                {!λ f → λ= (λ x → <–-inv-l B _ ∙ ap f (<–-inv-l A x))!}
    -}

module _ {{_ : UA}}{{_ : FunExt}}{a}{A₀ A₁ : ★_ a}{b} where
    Σ-fst≃ : ∀ (A : A₀ ≃ A₁)(B : A₁ → ★_ b) → Σ A₀ (B ∘ –> A) ≡ Σ A₁ B
    Σ-fst≃ A B = Σ≃ A (λ x → idp)

    Σ-fst= : ∀ (A : A₀ ≡ A₁)(B : A₁ → ★_ b) → Σ A₀ (B ∘ coe A) ≡ Σ A₁ B
    Σ-fst= A = Σ-fst≃ (coe-equiv A)

    Π-dom≃ : ∀ (A : A₀ ≃ A₁)(B : A₁ → ★_ b) → Π A₀ (B ∘ –> A) ≡ Π A₁ B
    Π-dom≃ A B = Π≃ A (λ x → idp)

    Π-dom= : ∀ (A : A₀ ≡ A₁)(B : A₁ → ★_ b) → Π A₀ (B ∘ coe A) ≡ Π A₁ B
    Π-dom= A = Π-dom≃ (coe-equiv A)

    -- variations where the equiv is transported backward on the right side

    Σ-fst≃′ : (A : A₁ ≃ A₀)(B : A₁ → ★_ b) → Σ A₁ B ≡ Σ A₀ (B ∘ <– A)
    Σ-fst≃′ A B = ! Σ-fst≃ (≃-sym A) B

    Σ-fst=′ : (A : A₁ ≡ A₀)(B : A₁ → ★_ b) → Σ A₁ B ≡ Σ A₀ (B ∘ coe! A)
    Σ-fst=′ A = Σ-fst≃′ (coe-equiv A)

    Π-dom≃′ : (A : A₁ ≃ A₀)(B : A₁ → ★_ b) → Π A₁ B ≡ Π A₀ (B ∘ <– A)
    Π-dom≃′ A B = ! Π-dom≃ (≃-sym A) B

    Π-dom=′ : (A : A₁ ≡ A₀)(B : A₁ → ★_ b) → Π A₁ B ≡ Π A₀ (B ∘ coe! A)
    Π-dom=′ A = Π-dom≃′ (coe-equiv A)

module _ {a b c} {A : ★_ a} {B : A → ★_ b} {C : Σ A B → ★_ c} where
    ΠΣ-curry-equiv : Π (Σ A B) C ≃ ((x : A) (y : B x) → C (x , y))
    ΠΣ-curry-equiv = equiv curry uncurry (λ _ → idp) (λ _ → idp)

    ΠΣ-curry : {{_ : UA}} → Π (Σ A B) C ≡ ((x : A) (y : B x) → C (x , y))
    ΠΣ-curry = ua ΠΣ-curry-equiv

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

module _ {{_ : UA}}{a b c}{A : ★_ a}{B : ★_ b}{C : A ⊎ B → ★_ c} where
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

module _ {a b c}{A : ★_ a}{B : A → ★_ b}{C : (x : A) → B x → ★_ c} where
    Σ-assoc-equiv : (Σ A (λ x → Σ (B x) (C x))) ≃ (Σ (Σ A B) (uncurry C))
    Σ-assoc-equiv = equiv (λ x → (fst x , fst (snd x)) , snd (snd x))
                          (λ x → fst (fst x) , snd (fst x) , snd x)
                          (λ y → idp)
                          (λ y → idp)

    Σ-assoc : {{_ : UA}} → (Σ A (λ x → Σ (B x) (C x))) ≡ (Σ (Σ A B) (uncurry C))
    Σ-assoc = ua Σ-assoc-equiv

module _ {a b}{A : ★_ a} {B : ★_ b} where
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

module _ {a b c} {A : ★_ a} {B : ★_ b} {C : ★_ c} where
    ×-assoc : {{_ : UA}} → (A × (B × C)) ≡ ((A × B) × C)
    ×-assoc = Σ-assoc

    ⊎-assoc-equiv : (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
    ⊎-assoc-equiv = equiv [inl: inl ∘ inl ,inr: [inl: inl ∘ inr ,inr: inr ] ]
                          [inl: [inl: inl ,inr: inr ∘ inl ] ,inr: inr ∘ inr ]
                          [inl: [inl: (λ x → idp) ,inr: (λ x → idp) ] ,inr: (λ x → idp) ]
                          [inl: (λ x → idp) ,inr: [inl: (λ x → idp) ,inr: (λ x → idp) ] ]

    ⊎-assoc : {{_ : UA}} → (A ⊎ (B ⊎ C)) ≡ ((A ⊎ B) ⊎ C)
    ⊎-assoc = ua ⊎-assoc-equiv

module _ {{_ : UA}}{{_ : FunExt}}{a}(A : 𝟘 → ★_ a) where
    Π𝟘-uniq : Π 𝟘 A ≡ Lift 𝟙
    Π𝟘-uniq = ua (equiv _ (λ _ ()) (λ _ → idp) (λ _ → λ= (λ())))

module _ {{_ : UA}}{{_ : FunExt}}(A : 𝟘 → ★₀) where
    Π𝟘-uniq₀ : Π 𝟘 A ≡ 𝟙
    Π𝟘-uniq₀ = ua (equiv _ (λ _ ()) (λ _ → idp) (λ _ → λ= (λ())))

module _ {{_ : UA}}{a}(A : 𝟙 → ★_ a) where
    Π𝟙-uniq : Π 𝟙 A ≡ A _
    Π𝟙-uniq = ua (equiv (λ f → f _) (λ x _ → x) (λ _ → idp) (λ _ → idp))

module _ {{_ : UA}}{a}(A : ★_ a) where
    Π𝟙-uniq′ : (𝟙 → A) ≡ A
    Π𝟙-uniq′ = Π𝟙-uniq (λ _ → A)

module _ {{_ : UA}}{{_ : FunExt}}(A : ★₀) where
    Π𝟘-uniq′ : (𝟘 → A) ≡ 𝟙
    Π𝟘-uniq′ = Π𝟘-uniq₀ (λ _ → A)

    𝟘→A≡𝟙 = Π𝟘-uniq′

module _ {{_ : FunExt}}{ℓ}(F G : 𝟘 → ★_ ℓ) where
    -- also by Π𝟘-uniq twice
    Π𝟘-uniq' : Π 𝟘 F ≡ Π 𝟘 G
    Π𝟘-uniq' = Π=′ 𝟘 (λ())

module _ {a ℓ} {A : 𝟘 → ★_ a} where
    Σ𝟘-lift∘fst-equiv : Σ 𝟘 A ≃ Lift {ℓ = ℓ} 𝟘
    Σ𝟘-lift∘fst-equiv = equiv (lift ∘ fst) (λ { (lift ()) }) (λ { (lift ()) }) (λ { (() , _) })

module _ {a} {A : 𝟘 → ★_ a} {{_ : UA}} where
    Σ𝟘-lift∘fst : Σ 𝟘 A ≡ Lift {ℓ = a} 𝟘
    Σ𝟘-lift∘fst = ua Σ𝟘-lift∘fst-equiv

module _ {A : 𝟘 → ★} where
    Σ𝟘-fst-equiv : Σ 𝟘 A ≃ 𝟘
    Σ𝟘-fst-equiv = equiv fst (λ()) (λ()) (λ { (() , _) })

    Σ𝟘-fst : {{_ : UA}} → Σ 𝟘 A ≡ 𝟘
    Σ𝟘-fst = ua Σ𝟘-fst-equiv

module _ {a}{A : 𝟙 → ★_ a} where
    Σ𝟙-snd-equiv : Σ 𝟙 A ≃ A _
    Σ𝟙-snd-equiv = equiv snd (_,_ _) (λ _ → idp) (λ _ → idp)

    Σ𝟙-snd : {{_ : UA}} → Σ 𝟙 A ≡ A _
    Σ𝟙-snd = ua Σ𝟙-snd-equiv

module _ {A : ★} where
    ⊎𝟘-inl-equiv : A ≃ (A ⊎ 𝟘)
    ⊎𝟘-inl-equiv = equiv inl [inl: id ,inr: (λ()) ] [inl: (λ _ → idp) ,inr: (λ()) ] (λ _ → idp)

    module _ {{_ : UA}} where
        ⊎𝟘-inl : A ≡ (A ⊎ 𝟘)
        ⊎𝟘-inl = ua ⊎𝟘-inl-equiv

        𝟘⊎-inr : A ≡ (𝟘 ⊎ A)
        𝟘⊎-inr = ⊎𝟘-inl ∙ ⊎-comm

        𝟙×-snd : (𝟙 × A) ≡ A
        𝟙×-snd = Σ𝟙-snd

        ×𝟙-fst : (A × 𝟙) ≡ A
        ×𝟙-fst = ×-comm ∙ 𝟙×-snd

        𝟘×-fst : (𝟘 × A) ≡ 𝟘
        𝟘×-fst = Σ𝟘-fst

        ×𝟘-snd : (A × 𝟘) ≡ 𝟘
        ×𝟘-snd = ×-comm ∙ Σ𝟘-fst

        -- old names
        A×𝟙≡A = ×𝟙-fst
        𝟙×A≡A = 𝟙×-snd
        𝟘⊎A≡A = 𝟘⊎-inr
        A⊎𝟘≡A = ⊎𝟘-inl
        𝟘×A≡𝟘 = 𝟘×-fst
        A×𝟘≡𝟘 = ×𝟘-snd

module _ {A : ★}{B : A → ★}{C : Σ A B → ★} where
    -- AC: Dependent axiom of choice
    -- In Type Theory it happens to be neither an axiom nor to be choosing anything.
    ΠΣ-comm-equiv : (∀ (x : A) → ∃ λ (y : B x) → C (x , y)) ≃ (∃ λ (f : Π A B) → ∀ (x : A) → C (x , f x))
    ΠΣ-comm-equiv = equiv (λ H → fst ∘ H , snd ∘ H) (λ H → < fst H , snd H >) (λ H → idp) (λ H → idp)

    ΠΣ-comm : {{_ : UA}}
            → (∀ (x : A) → ∃ λ (y : B x) → C (x , y)) ≡ (∃ λ (f : Π A B) → ∀ (x : A) → C (x , f x))
    ΠΣ-comm = ua ΠΣ-comm-equiv

module _ {ℓ}{A : 𝟚 → ★_ ℓ}{{_ : UA}}{{_ : FunExt}} where
  Σ𝟚-⊎ : Σ 𝟚 A ≡ (A 0₂ ⊎ A 1₂)
  Σ𝟚-⊎ = Σ-fst≃′ 𝟚≃𝟙⊎𝟙 _ ∙ dist-⊎-Σ ∙ ⊎= Σ𝟙-snd Σ𝟙-snd

  Π𝟚-× : Π 𝟚 A ≡ (A 0₂ × A 1₂)
  Π𝟚-× = Π-dom≃′ 𝟚≃𝟙⊎𝟙 _ ∙ dist-×-Π ∙ ×= (Π𝟙-uniq _) (Π𝟙-uniq _)

  Π𝟚F≡F₀×F₁ = Π𝟚-×

module _ {A : ★}{{_ : UA}}{{_ : FunExt}} where
  Σ𝟚-⊎′ : (𝟚 × A) ≡ (A ⊎ A)
  Σ𝟚-⊎′ = Σ𝟚-⊎

  Π𝟚→×′ : (𝟚 → A) ≡ (A × A)
  Π𝟚→×′ = Π𝟚-×

module _ {a}{A : ★_ a} where

  Σ≡x≃𝟙 : ∀ x → (Σ A (_≡_ x)) ≃ 𝟙
  Σ≡x≃𝟙 x = equiv (λ _ → _) (λ _ → x , idp) (λ _ → idp) (λ p → pair= (snd p) (tr-r≡ (snd p) idp))

  Σx≡≃𝟙 : ∀ x → (Σ A (flip _≡_ x)) ≃ 𝟙
  Σx≡≃𝟙 x = equiv (λ _ → _) (λ _ → x , idp) (λ _ → idp) (λ p →  pair= (! snd p)  ( tr-l≡ (! snd p) idp ∙
    ∙-refl (! (! (snd p))) ∙ !-inv (snd p)))

module _ {ab c}{A B : ★_ ab}{C : A → B → ★_ c}{{_ : UA}}{{_ : FunExt}} where

  Π⊎-equiv : (Π (A ⊎ B) [inl: (λ x → ∀ y → C x y) ,inr: (λ y → ∀ x → C x y) ]) ≃ ((t : 𝟚)(x : A)(y : B) → C x y)
  Π⊎-equiv = equiv (λ f → [0: (λ x y → f (inl x) y) 1: ((λ x y → f (inr y) x)) ])
                   (λ f → [inl: f 0₂ ,inr: flip (f 1₂) ])
                   (λ f → λ= [0: idp 1: idp ])
                   (λ f → λ= [inl: (λ x → idp) ,inr: (λ x → idp) ])

  Π⊎ : (Π (A ⊎ B) [inl: (λ x → ∀ y → C x y) ,inr: (λ y → ∀ x → C x y) ]) ≡ ((t : 𝟚)(x : A)(y : B) → C x y)
  Π⊎ = ua Π⊎-equiv

module _ {ab c}{A B : ★_ ab}{C : ★_ c}{{_ : UA}}{{_ : FunExt}} where
  Π⊎′ : (Π (A ⊎ B) [inl: const (B → C) ,inr: const (A → C) ]) ≡ (𝟚 → A → B → C)
  Π⊎′ = Π⊎

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

  Maybe≃Lift𝟙⊎ : Maybe A ≃ (Lift {ℓ = a} 𝟙 ⊎ A)
  Maybe≃Lift𝟙⊎ = equiv (maybe inr (inl _))
                        [inl: const nothing ,inr: just ]
                        [inl: (λ _ → idp)   ,inr: (λ _ → idp) ]
                        (maybe (λ _ → idp) idp)

  Vec0≃𝟙 : Vec A 0 ≃ 𝟙
  Vec0≃𝟙 = equiv _ (const []) (λ _ → idp) (λ { [] → idp })

  Vec0≃Lift𝟙 : Vec A 0 ≃ Lift {ℓ = a} 𝟙
  Vec0≃Lift𝟙 = equiv _ (const []) (λ _ → idp) (λ { [] → idp })

  Vec∘suc≃× : ∀ {n} → Vec A (suc n) ≃ (A × Vec A n)
  Vec∘suc≃× = equiv (λ { (x ∷ xs) → x , xs }) (λ { (x , xs) → x ∷ xs })
                    (λ { (x , xs) → idp }) (λ { (x ∷ xs) → idp })

  module _ {{_ : UA}} where

    Maybe≡𝟙⊎ : Maybe A ≡ (𝟙 ⊎ A)
    Maybe≡𝟙⊎ = ua Maybe≃𝟙⊎

    Maybe≡Lift𝟙⊎ : Maybe A ≡ (Lift {ℓ = a} 𝟙 ⊎ A)
    Maybe≡Lift𝟙⊎ = ua Maybe≃Lift𝟙⊎

    Vec0≡Lift𝟙 : Vec A 0 ≡ Lift {ℓ = a} 𝟙
    Vec0≡Lift𝟙 = ua Vec0≃Lift𝟙

    Vec∘suc≡× : ∀ {n} → Vec A (suc n) ≡ (A × Vec A n)
    Vec∘suc≡× = ua Vec∘suc≃×

module _ {A : ★}{{_ : UA}} where
    Vec0≡𝟙 : Vec A 0 ≡ 𝟙
    Vec0≡𝟙 = ua Vec0≃𝟙

Fin0≃𝟘 : Fin 0 ≃ 𝟘
Fin0≃𝟘 = equiv (λ ()) (λ ()) (λ ()) (λ ())

Fin1≃𝟙 : Fin 1 ≃ 𝟙
Fin1≃𝟙 = equiv _ (λ _ → zero) (λ _ → idp) β
  where β : (_ : Fin 1) → _
        β zero = idp
        β (suc ())

module _ {{_ : UA}} where
    Fin0≡𝟘 : Fin 0 ≡ 𝟘
    Fin0≡𝟘 = ua Fin0≃𝟘

    Fin1≡𝟙 : Fin 1 ≡ 𝟙
    Fin1≡𝟙 = ua Fin1≃𝟙

Fin∘suc≃𝟙⊎Fin : ∀ {n} → Fin (suc n) ≃ (𝟙 ⊎ Fin n)
Fin∘suc≃𝟙⊎Fin = equiv [zero: inl _ ,suc: inr ] [inl: (λ _ → zero) ,inr: suc ]
  [inl: (λ _ → idp) ,inr: (λ _ → idp) ]
  [zero: idp ,suc: (λ _ → idp) ]

Fin∘suc≡𝟙⊎Fin : ∀ {{_ : UA}}{n} → Fin (suc n) ≡ (𝟙 ⊎ Fin n)
Fin∘suc≡𝟙⊎Fin = ua Fin∘suc≃𝟙⊎Fin

Fin-⊎-+ : ∀ {{_ : UA}} {m n} → (Fin m ⊎ Fin n) ≡ Fin (m ℕ.+ n)
Fin-⊎-+ {zero}  = ⊎= Fin0≡𝟘 idp ∙ ⊎-comm ∙ ! ⊎𝟘-inl
Fin-⊎-+ {suc m} = ⊎= Fin∘suc≡𝟙⊎Fin idp ∙ ! ⊎-assoc ∙ ap (_⊎_ 𝟙) Fin-⊎-+ ∙ ! Fin∘suc≡𝟙⊎Fin

Fin-×-* : ∀ {{_ : UA}} {m n} → (Fin m × Fin n) ≡ Fin (m ℕ.* n)
Fin-×-* {zero}  = ×= Fin0≡𝟘 idp ∙ Σ𝟘-fst ∙ ! Fin0≡𝟘
Fin-×-* {suc m} = ×= Fin∘suc≡𝟙⊎Fin idp ∙ dist-⊎-× ∙ ⊎= Σ𝟙-snd Fin-×-* ∙ Fin-⊎-+

Fin-→-^ : ∀ {{_ : UA}}{{_ : FunExt}}{m n} → (Fin m → Fin n) ≡ Fin (n ℕ.^ m)
Fin-→-^ {zero}  = →= Fin0≡𝟘 idp ∙ Π𝟘-uniq′ _ ∙ ⊎𝟘-inl ∙ ap (_⊎_ 𝟙) (! Fin0≡𝟘)
                  ∙ ! Fin∘suc≡𝟙⊎Fin
Fin-→-^ {suc m} = →= Fin∘suc≡𝟙⊎Fin idp ∙ dist-×-→ ∙ ×= (Π𝟙-uniq _) Fin-→-^ ∙ Fin-×-*

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
Fin⊎-injective zero    f = ⊎𝟘-inl ∙ ⊎-comm ∙  ⊎= (! Fin0≡𝟘) idp
                       ∙ f ∙ (⊎= Fin0≡𝟘 idp ∙ ⊎-comm) ∙ ! ⊎𝟘-inl
Fin⊎-injective (suc n) f = Fin⊎-injective n (Maybe-injective
   (Maybe≡𝟙⊎ ∙ ⊎-assoc ∙ ⊎= (! Fin∘suc≡𝟙⊎Fin) idp ∙ f
   ∙ ⊎= Fin∘suc≡𝟙⊎Fin idp ∙ ! ⊎-assoc ∙ ! Maybe≡𝟙⊎))

Lift≃id : ∀ {a} {A : ★_ a} → Lift {a} {a} A ≃ A
Lift≃id = equiv lower lift (λ _ → idp) (λ { (lift x) → idp })

module _ {{_ : UA}} where
    Fin-≡-≡1₂ : ∀ b → Fin (𝟚▹ℕ b) ≡ (b ≡ 1₂)
    Fin-≡-≡1₂ 1₂ = Fin1≡𝟙 ∙ ua (Is-contr-to-Is-equiv.𝟙≃ (Ω₁-set-to-contr 𝟚-is-set 1₂))
    Fin-≡-≡1₂ 0₂ = ua (equiv (λ ()) (λ ()) (λ ()) (λ ()))

    Fin-≡-≡0₂ : ∀ b → Fin (𝟚▹ℕ (not b)) ≡ (b ≡ 0₂)
    Fin-≡-≡0₂ b = Fin-≡-≡1₂ (not b) ∙ ! –>-paths-equiv twist-equiv

    ✓-∧-× : ∀ x y → ✓ (x ∧ y) ≡ (✓ x × ✓ y)
    ✓-∧-× 1₂ y = ! 𝟙×-snd
    ✓-∧-× 0₂ y = ! 𝟘×-fst

    count-≡ : ∀ {a} {A : ★_ a} (p : A → 𝟚) x → Fin (𝟚▹ℕ (p x)) ≡ (p x ≡ 1₂)
    count-≡ p x = Fin-≡-≡1₂ (p x)

    Lift≡id : ∀ {a} {A : ★_ a} → Lift {a} {a} A ≡ A
    Lift≡id = ua Lift≃id

    Π𝟙F≡F : ∀ {ℓ} {F : 𝟙 → ★_ ℓ} → Π 𝟙 F ≡ F _
    Π𝟙F≡F = ua (equiv (λ x → x _) const (λ _ → idp) (λ _ → idp))

    𝟙→A≡A : ∀ {ℓ} {A : ★_ ℓ} → (𝟙 → A) ≡ A
    𝟙→A≡A = Π𝟙F≡F

    not-𝟚≡𝟚 : 𝟚 ≡ 𝟚
    not-𝟚≡𝟚 = twist

    Maybe𝟘≡𝟙 : Maybe 𝟘 ≡ 𝟙
    Maybe𝟘≡𝟙 = Maybe≡𝟙⊎ ∙ ! ⊎𝟘-inl

    Maybe∘Maybe^≡Maybe^∘Maybe : ∀ {a} {A : ★_ a} n → Maybe (Maybe^ n A) ≡ Maybe^ n (Maybe A)
    Maybe∘Maybe^≡Maybe^∘Maybe zero    = idp
    Maybe∘Maybe^≡Maybe^∘Maybe (suc n) = ap Maybe (Maybe∘Maybe^≡Maybe^∘Maybe n)

    Maybe^𝟘≡Fin : ∀ n → Maybe^ n 𝟘 ≡ Fin n
    Maybe^𝟘≡Fin zero    = ! Fin0≡𝟘
    Maybe^𝟘≡Fin (suc n) = ap Maybe (Maybe^𝟘≡Fin n) ∙ ! Fin∘suc≡Maybe∘Fin

    Maybe^𝟙≡Fin1+ : ∀ n → Maybe^ n 𝟙 ≡ Fin (suc n)
    Maybe^𝟙≡Fin1+ n = ap (Maybe^ n) (! Maybe𝟘≡𝟙) ∙ ! Maybe∘Maybe^≡Maybe^∘Maybe n ∙ Maybe^𝟘≡Fin (suc n)

    Maybe-⊎ : ∀ {a} {A B : ★_ a} → (Maybe A ⊎ B) ≡ Maybe (A ⊎ B)
    Maybe-⊎ {a} = ⊎= Maybe≡Lift𝟙⊎ idp ∙ ! ⊎-assoc ∙ ! Maybe≡Lift𝟙⊎

    Maybe^-⊎-+ : ∀ {A} m n → (Maybe^ m 𝟘 ⊎ Maybe^ n A) ≡ Maybe^ (m + n) A
    Maybe^-⊎-+ zero    n = ! 𝟘⊎-inr
    Maybe^-⊎-+ (suc m) n = Maybe-⊎ ∙ ap Maybe (Maybe^-⊎-+ m n)

module _ {A : Set} {p q : A → 𝟚} where
    ΣAP¬Q : Set
    ΣAP¬Q = Σ A (λ x → p x ≡ 1₂ × q x ≡ 0₂)

    ΣA¬PQ : Set
    ΣA¬PQ = Σ A (λ x → p x ≡ 0₂ × q x ≡ 1₂)

    module EquivalentSubsets (e : ΣAP¬Q ≡ ΣA¬PQ) where

      f' : ΣAP¬Q → ΣA¬PQ
      f' = coe e

      f-1' : ΣA¬PQ → ΣAP¬Q
      f-1' = coe! e

      f-1f' : ∀ x → f-1' (f' x) ≡ x
      f-1f' = coe!-inv-l e

      ff-1' : ∀ x → f' (f-1' x) ≡ x
      ff-1' = coe!-inv-r e

      f   : (x : A) → p x ≡ 1₂ → q x ≡ 0₂ → ΣA¬PQ
      f x px qx = f' (x , (px , qx))

      f-1 : (x : A) → p x ≡ 0₂ → q x ≡ 1₂ → ΣAP¬Q
      f-1 x px qx = f-1' (x , (px , qx))

      f-1f : ∀ x px nqx →
             let y = snd (f x px nqx) in fst (f-1 (fst (f x px nqx)) (fst y) (snd y)) ≡ x
      f-1f x px nqx = ≡.cong fst (f-1f' (x , (px , nqx)))

      ff-1 : ∀ x px nqx →
             let y = snd (f-1 x px nqx) in fst (f (fst (f-1 x px nqx)) (fst y) (snd y)) ≡ x
      ff-1 x px nqx = ≡.cong fst (ff-1' (x , (px , nqx)))

      π' : (x : A) (px qx : 𝟚) → p x ≡ px → q x ≡ qx → A
      π' x 1₂ 1₂ px qx = x
      π' x 1₂ 0₂ px qx = fst (f x px qx)
      π' x 0₂ 1₂ px qx = fst (f-1 x px qx)
      π' x 0₂ 0₂ px qx = x

      π : A → A
      π x = π' x (p x) (q x) ≡.refl ≡.refl

      0≢1 : 0₂ ≢ 1₂
      0≢1 ()

      π01 : ∀ x px qx (ppx : p x ≡ px) (qqx : q x ≡ qx) (px0 : p x ≡ 0₂) (qx1 : q x ≡ 1₂) → π' x px qx ppx qqx ≡ π' x 0₂ 1₂ px0 qx1
      π01 x 1₂ _  ppx qqx px0 qx1 = 𝟘-elim (0≢1 (≡.trans (≡.sym px0) ppx))
      π01 x 0₂ 1₂ ppx qqx px0 qx1 = ≡.ap₂ (λ z1 z2 → fst (f-1 x z1 z2)) (UIP-set 𝟚-is-set ppx px0) (UIP-set 𝟚-is-set qqx qx1)
      π01 x 0₂ 0₂ ppx qqx px0 qx1 = 𝟘-elim (0≢1 (≡.trans (≡.sym qqx) qx1))

      π10 : ∀ x px qx (ppx : p x ≡ px) (qqx : q x ≡ qx) (px1 : p x ≡ 1₂) (qx0 : q x ≡ 0₂) → π' x px qx ppx qqx ≡ π' x 1₂ 0₂ px1 qx0
      π10 x 0₂ _  ppx qqx px1 qx0 = 𝟘-elim (0≢1 (≡.trans (≡.sym ppx) px1))
      π10 x 1₂ 0₂ ppx qqx px1 qx0 = ≡.ap₂ (λ z1 z2 → fst (f x z1 z2)) (UIP-set 𝟚-is-set ppx px1) (UIP-set 𝟚-is-set qqx qx0)
      π10 x 1₂ 1₂ ppx qqx px1 qx0 = 𝟘-elim (0≢1 (≡.trans (≡.sym qx0) qqx))

      π'bb : ∀ {b} x (px : p x ≡ b) (qx : q x ≡ b) ppx qqx ([ppx] : p x ≡ ppx) ([qqx] : q x ≡ qqx) → π' x ppx qqx [ppx] [qqx] ≡ x
      π'bb x px qx 1₂ 1₂ [ppx] [qqx] = ≡.refl
      π'bb x px qx 1₂ 0₂ [ppx] [qqx] = 𝟘-elim (0≢1 (≡.trans (≡.sym [qqx]) (≡.trans qx (≡.trans (≡.sym px) [ppx]))))
      π'bb x px qx 0₂ 1₂ [ppx] [qqx] = 𝟘-elim (0≢1 (≡.trans (≡.sym [ppx]) (≡.trans px (≡.trans (≡.sym qx) [qqx]))))
      π'bb x px qx 0₂ 0₂ [ppx] [qqx] = ≡.refl

      ππ' : ∀ x px qx [px] [qx] → let y = (π' x px qx [px] [qx]) in π' y (p y) (q y) ≡.refl ≡.refl ≡ x
      ππ' x 1₂ 1₂ px qx = π'bb x px qx (p x) (q x) ≡.refl ≡.refl
      ππ' x 1₂ 0₂ px qx = let fx = f x px qx in let pfx = fst (snd fx) in let qfx = snd (snd fx) in ≡.trans (π01 (fst fx) (p (fst fx)) (q (fst fx)) ≡.refl ≡.refl pfx qfx) (f-1f x px qx)
      ππ' x 0₂ 1₂ px qx = let fx = f-1 x px qx in let pfx = fst (snd fx) in let qfx = snd (snd fx) in ≡.trans (π10 (fst fx) (p (fst fx)) (q (fst fx)) ≡.refl ≡.refl pfx qfx) (ff-1 x px qx)
      ππ' x 0₂ 0₂ px qx = π'bb x px qx (p x) (q x) ≡.refl ≡.refl

      ππ : ∀ x → π (π x) ≡ x
      ππ x = ππ' x (p x) (q x) ≡.refl ≡.refl

      prop' : ∀ px qx x ([px] : p x ≡ px) ([qx] : q x ≡ qx) → q (π' x px qx [px] [qx]) ≡ px
      prop' 1₂ 1₂ x px qx = qx
      prop' 1₂ 0₂ x px qx = snd (snd (f x px qx))
      prop' 0₂ 1₂ x px qx = snd (snd (f-1 x px qx))
      prop' 0₂ 0₂ x px qx = qx

      prop'' : ∀ x → p x ≡ q (π x)
      prop'' x = ≡.sym (prop' (p x) (q x) x ≡.refl ≡.refl)

      prop : {{_ : FunExt}} → p ≡ q ∘ π
      prop = λ= prop''
-- -}
-- -}
-- -}
-- -}
