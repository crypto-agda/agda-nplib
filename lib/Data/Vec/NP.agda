{-# OPTIONS --copatterns #-}
-- NOTE with-K
module Data.Vec.NP where

open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties
import Algebra.FunctionProperties.Eq
open import Type hiding (Type)
import Level as L
open import Category.Applicative
open import Data.Nat.NP using (ℕ; suc; zero; _+_; _*_; 2*; module ℕ° ; +-interchange ; _≤_)
open import Data.Nat.Properties using (_+-mono_)
open import Data.Fin hiding (_≤_) renaming (_+_ to _+ᶠ_)
open import Data.Vec using (Vec; []; _∷_; head; tail; replicate; tabulate; foldr; _++_; lookup; splitAt; take; drop; sum; _∷ʳ_; concat)
import Data.Fin.Properties as F
open import Data.Bit
open import Data.Bool using (Bool; if_then_else_)
open import Data.Product hiding (zip; swap) renaming (proj₁ to fst; proj₂ to snd; map to ×-map)
open import Function.NP
open import Relation.Binary
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_; ap; ap₂; _∙_; !_) renaming (refl to idp)
import Data.Vec.Equality

module FunVec {a} {A : Type a} where
    _→ᵛ_ : ℕ → ℕ → Type a
    i →ᵛ o = Vec A i → Vec A o

ap-∷ : ∀ {a} {A : Type a} {n}
         {x y : A} {xs ys : Vec A n} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
ap-∷ = ap₂ _∷_

module waiting-for-a-fix-in-the-stdlib where

    infixl 4 _⊛_

    _⊛_ : ∀ {a b n} {A : Type a} {B : Type b} →
          Vec (A → B) n → Vec A n → Vec B n
    _⊛_ {n = zero}  fs xs = []
    _⊛_ {n = suc n} fs xs = head fs (head xs) ∷ (tail fs ⊛ tail xs)

    applicative : ∀ {a n} → RawApplicative (λ (A : Type a) → Vec A n)
    applicative = record
      { pure = replicate
      ; _⊛_  = _⊛_
      }

    map : ∀ {a b n} {A : Type a} {B : Type b} →
          (A → B) → Vec A n → Vec B n
    map f xs = replicate f ⊛ xs

    zipWith : ∀ {a b c n} {A : Type a} {B : Type b} {C : Type c} →
              (A → B → C) → Vec A n → Vec B n → Vec C n
    zipWith _⊕_ xs ys = replicate _⊕_ ⊛ xs ⊛ ys

    zip : ∀ {a b n} {A : Type a} {B : Type b} →
          Vec A n → Vec B n → Vec (A × B) n
    zip = zipWith _,_

    tabulate-∘ : ∀ {n a b} {A : Type a} {B : Type b}
                 (f : A → B) (g : Fin n → A) →
                 tabulate (f ∘ g) ≡ map f (tabulate g)
    tabulate-∘ {zero}  f g = idp
    tabulate-∘ {suc n} f g = ap (_∷_ _) (tabulate-∘ f (g ∘ suc))

    tabulate-ext : ∀ {n a}{A : Type a}{f g : Fin n → A} → f ≗ g → tabulate f ≡ tabulate g
    tabulate-ext {zero}  f≗g = idp
    tabulate-ext {suc n} f≗g = ap-∷ (f≗g zero) (tabulate-ext (f≗g ∘ suc))

    -- map is functorial.

    map-id= : ∀ {a n} {A : Type a}{f : A → A}
             → f ≗ id → map f ≗ id {A = Vec A n}
    map-id= f= []       = idp
    map-id= f= (x ∷ xs) = ap-∷ (f= x) (map-id= f= xs)

    map-id : ∀ {a n} {A : Type a} → map id ≗ id {A = Vec A n}
    map-id = map-id= (λ _ → idp)

    map-∘= : ∀ {a b c n} {A : Type a} {B : Type b} {C : Type c}
               {f : B → C}{g : A → B}{h : A → C} →
               f ∘ g ≗ h →
               _≗_ {A = Vec A n} (map f ∘ map g) (map h)
    map-∘= fg= []       = idp
    map-∘= fg= (x ∷ xs) = ap-∷ (fg= x) (map-∘= fg= xs)

    map-∘ : ∀ {a b c n} {A : Type a} {B : Type b} {C : Type c}
              (f : B → C) (g : A → B) →
              _≗_ {A = Vec A n} (map (f ∘ g)) (map f ∘ map g)
    map-∘ f g v = ! map-∘= (λ _ → idp) v

    map-ext : ∀ {a b} {A : Type a} {B : Type b} {f g : A → B} {n} → f ≗ g → map f ≗ map {n = n} g
    map-ext f≗g []       = idp
    map-ext f≗g (x ∷ xs) = ap-∷ (f≗g x) (map-ext f≗g xs)

open waiting-for-a-fix-in-the-stdlib public

module With≈
    {a ℓ ℓ'}{A : Type a}
    (_≈_ : A → A → Type ℓ)
    {_≈ᵛ_ : ∀ {n}(xs ys : Vec A n) → Type ℓ'}
    ([]-cong  : [] ≈ᵛ [])
    (_∷-cong_ : ∀ {n} {x¹} {xs¹ : Vec A n} {x²} {xs² : Vec A n}
                  (x¹≈x² : x¹ ≈ x²) (xs¹≈xs² : xs¹ ≈ᵛ xs²) →
                  (x¹ ∷ xs¹) ≈ᵛ (x² ∷ xs²))
  where
  open Algebra.FunctionProperties

  module _ {_∙_ _∙∙_ : A → A → A}
           (assoc : ∀ x y z → ((x ∙ y) ∙∙ z) ≈ (x ∙ (y ∙∙ z))) where
    private
      _∙ᵛ_ _∙∙ᵛ_ : ∀ {n}(xs ys : Vec A n) → Vec A n
      _∙ᵛ_  = zipWith _∙_
      _∙∙ᵛ_ = zipWith _∙∙_

    zipWith-assoc : ∀ {n} (xs ys zs : Vec A n) → ((xs ∙ᵛ ys) ∙∙ᵛ zs) ≈ᵛ (xs ∙ᵛ (ys ∙∙ᵛ zs))
    zipWith-assoc [] [] [] = []-cong
    zipWith-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs)
       = assoc x y z ∷-cong (zipWith-assoc xs ys zs)

  module _ {_∙_ : A → A → A} where
    module _ (∙-comm : Commutative _≈_ _∙_) where
      zipWith-comm : ∀ {n} → Commutative _≈ᵛ_ (zipWith {n = n} _∙_)
      zipWith-comm [] [] = []-cong
      zipWith-comm (x ∷ xs) (y ∷ ys) = ∙-comm x y ∷-cong zipWith-comm xs ys

    module _ {ε : A} where
      module _ (∙-id-left : LeftIdentity _≈_ ε _∙_) where
        zipWith-id-left : ∀ {n} → LeftIdentity _≈ᵛ_ (replicate ε) (zipWith {n = n} _∙_)
        zipWith-id-left [] = []-cong
        zipWith-id-left (x ∷ xs) = ∙-id-left x ∷-cong zipWith-id-left xs

      module _ (∙-id-right : RightIdentity _≈_ ε _∙_) where
        zipWith-id-right : ∀ {n} → RightIdentity _≈ᵛ_ (replicate ε) (zipWith {n = n} _∙_)
        zipWith-id-right [] = []-cong
        zipWith-id-right (x ∷ xs) = ∙-id-right x ∷-cong zipWith-id-right xs

      module _ {_⁻¹ : A → A}
               (inverse : LeftInverse _≈_ ε _⁻¹ _∙_) where
        zipWith-left-inverse : ∀ {n} → LeftInverse _≈ᵛ_ (replicate ε) (map _⁻¹) (zipWith {n = n} _∙_)
        zipWith-left-inverse [] = []-cong
        zipWith-left-inverse (x ∷ xs) = inverse x ∷-cong zipWith-left-inverse xs

      module _ {_⁻¹ : A → A}
               (inverse : RightInverse _≈_ ε _⁻¹ _∙_) where
        zipWith-right-inverse : ∀ {n} → RightInverse _≈ᵛ_ (replicate ε) (map _⁻¹) (zipWith {n = n} _∙_)
        zipWith-right-inverse [] = []-cong
        zipWith-right-inverse (x ∷ xs) = inverse x ∷-cong zipWith-right-inverse xs

module WithSetoid {c ℓ} (S : Setoid c ℓ) where
  A = Setoid.Carrier S
  open Setoid S
  V = Vec A
  module V≈ = Data.Vec.Equality.Equality S
  open Algebra.FunctionProperties
  open V≈ hiding (_≈_)
  _≈ᵛ_ : ∀ {n} → V n → V n → Type _
  xs ≈ᵛ ys = V≈._≈_ xs ys

  open With≈ _≈_ {_≈ᵛ_} []-cong (λ x y → x ∷-cong y) public

  module _ {f : A → A} (f-cong : f Preserves _≈_ ⟶ _≈_) where
    map-cong : ∀ {n} → map {n = n} f Preserves _≈ᵛ_ ⟶ _≈ᵛ_
    map-cong []-cong = []-cong
    map-cong (x≈y ∷-cong xs≈ys) = f-cong x≈y ∷-cong map-cong xs≈ys

  module _ {f : A → A → A} (f-cong : f Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_) where
    zipWith-cong : ∀ {n} → zipWith {n = n} f Preserves₂ _≈ᵛ_ ⟶ _≈ᵛ_ ⟶ _≈ᵛ_
    zipWith-cong []-cong []-cong = []-cong
    zipWith-cong (x≈y ∷-cong xs≈ys) (z≈t ∷-cong zs≈ts) = f-cong x≈y z≈t ∷-cong zipWith-cong xs≈ys zs≈ts

∷= : ∀ {a}{A : Type a}{n x} {xs : Vec A n} {y} {ys : Vec A n}
       (p : x ≡ y) (q : xs ≡ ys) →
        x ∷ xs ≡ y ∷ ys
∷= idp idp = idp

module With≡ {a}{A : Type a} where
  open With≈ (_≡_ {A = A}) {_≡_} idp (λ x¹≈x² xs¹≈xs² → ∷= x¹≈x² xs¹≈xs²) public

module LiftSemigroup {c ℓ} (Sg : Semigroup c ℓ) where
    module Sg = Semigroup Sg
    open WithSetoid Sg.setoid public

    _∙ᵛ_ : ∀ {n} → V n → V n → V n
    _∙ᵛ_ = zipWith Sg._∙_

    -- this should be in Data.Vec.Equality
    isEquivalence : ∀ {n} → IsEquivalence (_≈ᵛ_ {n})
    isEquivalence = record { refl = λ {xs} → V≈.refl xs
                           ; sym = V≈.sym ; trans = V≈.trans }

    isSemigroup : ∀ {n} → IsSemigroup (_≈ᵛ_ {n}) _∙ᵛ_
    isSemigroup = record { isEquivalence = isEquivalence
                                       ; assoc = zipWith-assoc Sg.assoc
                                       ; ∙-cong = zipWith-cong Sg.∙-cong }

    semigroup : ∀ n → Semigroup c (ℓ L.⊔ c)
    semigroup n = record { isSemigroup = isSemigroup {n} }

module LiftMonoid {c ℓ} (M : Monoid c ℓ) where
    module M = Monoid M
    open LiftSemigroup M.semigroup public

    εᵛ : ∀ {n} → V n
    εᵛ = replicate M.ε

    isMonoid : ∀ {n} → IsMonoid (_≈ᵛ_ {n}) _∙ᵛ_ εᵛ
    isMonoid = record { isSemigroup = isSemigroup
                      ; identity = zipWith-id-left (fst M.identity)
                                 , zipWith-id-right (snd M.identity) }

    monoid : ℕ → Monoid c (ℓ L.⊔ c)
    monoid n = record { isMonoid = isMonoid {n} }

module LiftCommutativeMonoid {c ℓ} (CM : CommutativeMonoid c ℓ) where
    module CM = CommutativeMonoid CM
    open LiftMonoid CM.monoid public

    isCommutativeMonoid : ∀ {n} → IsCommutativeMonoid (_≈ᵛ_ {n}) _∙ᵛ_ εᵛ
    isCommutativeMonoid =
       record { isSemigroup = isSemigroup
                  ; identityˡ = zipWith-id-left  CM.identityˡ
                  ; comm = zipWith-comm CM.comm }

    commutative-monoid : ℕ → CommutativeMonoid c (ℓ L.⊔ c)
    commutative-monoid n = record { isCommutativeMonoid = isCommutativeMonoid {n} }

module LiftGroup {c ℓ} (G : Group c ℓ) where
    module G = Group G
    open LiftMonoid G.monoid public

    _⁻¹ᵛ : ∀ {n} → V n → V n
    _⁻¹ᵛ = map G._⁻¹

    isGroup : ∀ {n} → IsGroup (_≈ᵛ_ {n}) _∙ᵛ_ εᵛ _⁻¹ᵛ
    isGroup = record { isMonoid = isMonoid
                                ; inverse = (zipWith-left-inverse (fst G.inverse))
                                                , (zipWith-right-inverse (snd G.inverse))
                                ; ⁻¹-cong = map-cong G.⁻¹-cong }

    group : ℕ → Group c _
    group n = record { isGroup = isGroup {n} }

module LiftAbelianGroup {c ℓ} (AG : AbelianGroup c ℓ) where
    module AG = AbelianGroup AG
    open LiftGroup AG.group public

    isAbelianGroup : ∀ {n} → IsAbelianGroup (_≈ᵛ_ {n}) _∙ᵛ_ εᵛ _⁻¹ᵛ
    isAbelianGroup = record { isGroup = isGroup ; comm = zipWith-comm AG.comm }

    abelianGroup : ℕ → AbelianGroup c _
    abelianGroup n = record { isAbelianGroup = isAbelianGroup {n} }

open Algebra.FunctionProperties.Eq.Implicits

-- Trying to get rid of the foldl in the definition of reverse and
-- without using equations on natural numbers.
-- In the end that's not very convincing.
module Alternative-Reverse where
    rev-+ : ℕ → ℕ → ℕ
    rev-+ zero    = id
    rev-+ (suc x) = rev-+ x ∘ suc

    rev-app : ∀ {a} {A : Type a} {m n} →
              Vec A n → Vec A m → Vec A (rev-+ n m)
    rev-app []       = id
    rev-app (x ∷ xs) = rev-app xs ∘ _∷_ x

    rev-aux : ∀ {a} {A : Type a} {m} n →
              Vec A (rev-+ n zero) →
              (∀ {m} → A → Vec A (rev-+ n m) → Vec A (rev-+ n (suc m))) →
              Vec A m → Vec A (rev-+ n m)
    rev-aux m acc op []       = acc
    rev-aux m acc op (x ∷ xs) = rev-aux (suc m) (op x acc) op xs

    alt-reverse : ∀ {a n} {A : Type a} → Vec A n → Vec A n
    alt-reverse = rev-aux 0 [] _∷_

countᶠ : ∀ {n a} {A : Type a} → (A → Bool) → Vec A n → Fin (suc n)
countᶠ pred = foldr (Fin ∘ suc) (λ x → if pred x then suc else inject₁) zero

count : ∀ {n a} {A : Type a} → (A → Bool) → Vec A n → ℕ
count pred = toℕ ∘ countᶠ pred

RewireTbl : (i o : ℕ) → ★₀
RewireTbl i o = Vec (Fin i) o

sum-∷ʳ : ∀ {n} x (xs : Vec ℕ n) → sum (xs ∷ʳ x) ≡ sum xs + x
sum-∷ʳ x []        = ℕ°.+-comm x 0
sum-∷ʳ x (x₁ ∷ xs) = ap (_+_ x₁) (sum-∷ʳ x xs) ∙ !(ℕ°.+-assoc x₁ (sum xs) x)

sum-distribˡ : ∀ {A : ★₀} {n} f k (xs : Vec A n) → sum (map (λ x → k * f x) xs) ≡ k * sum (map f xs)
sum-distribˡ f k [] = ℕ°.*-comm 0 k
sum-distribˡ f k (x ∷ xs) rewrite sum-distribˡ f k xs = !(fst ℕ°.distrib k _ _)

sum-linear : ∀ {A : ★₀} {n} f g (xs : Vec A n) → sum (map (λ x → f x + g x) xs) ≡ sum (map f xs) + sum (map g xs)
sum-linear f g [] = idp
sum-linear f g (x ∷ xs) rewrite sum-linear f g xs = +-interchange (f x) (g x) (sum (map f xs)) (sum (map g xs))

sum-mono : ∀ {A : ★₀} {n f g} (mono : ∀ x → f x ≤ g x)(xs : Vec A n) → sum (map f xs) ≤ sum (map g xs)
sum-mono f≤°g [] = Data.Nat.NP.z≤n
sum-mono f≤°g (x ∷ xs) = f≤°g x +-mono sum-mono f≤°g xs

module _ {a} {A : Type a} where
  -- Exchange elements at positions 0 and 1 of a given vector
  -- (this only apply if the vector is long enough).
  0↔1 : ∀ {n} → Vec A n → Vec A n
  0↔1 (x₀ ∷ x₁ ∷ xs) = x₁ ∷ x₀ ∷ xs
  0↔1 xs = xs

module _ {a} {A : Type a} where
  count-++ : ∀ {m n} (pred : A → Bool) (xs : Vec A m) (ys : Vec A n)
              → count pred (xs ++ ys) ≡ count pred xs + count pred ys
  count-++ pred [] ys = idp
  count-++ pred (x ∷ xs) ys with pred x
  ... | 1b rewrite count-++ pred xs ys = idp
  ... | 0b rewrite F.inject₁-lemma (countᶠ pred (xs ++ ys))
                    | F.inject₁-lemma (countᶠ pred xs) | count-++ pred xs ys = idp

  ext-countᶠ : ∀ {n} {f g : A → Bool} → f ≗ g → (xs : Vec A n) → countᶠ f xs ≡ countᶠ g xs
  ext-countᶠ f≗g [] = idp
  ext-countᶠ f≗g (x ∷ xs) rewrite ext-countᶠ f≗g xs | f≗g x = idp

  filter : ∀ {n} (pred : A → Bool) (xs : Vec A n) → Vec A (count pred xs)
  filter pred [] = []
  filter pred (x ∷ xs) with pred x
  ... | 1b = x ∷ filter pred xs
  ... | 0b rewrite F.inject₁-lemma (countᶠ pred xs) = filter pred xs

  transpose : ∀ {m n} → Vec (Vec A m) n → Vec (Vec A n) m
  transpose [] = replicate []
  transpose (xs ∷ xss) = zipWith _∷_ xs (transpose xss)

  vap : ∀ {m b} {B : Type b} (f : Vec A m → B)
          → ∀ {n} → Vec (Vec A n) m → Vec B n
  vap f = map f ∘ transpose

  infixl 2 _‼_
  _‼_ : ∀ {n} → Vec A n → Fin n → A
  _‼_ = flip lookup

  η : ∀ {n} → Vec A n → Vec A n
  η = tabulate ∘ _‼_

  η′ : ∀ {n} → Vec A n → Vec A n
  η′ {zero}  = λ _ → []
  η′ {suc n} = λ xs → head xs ∷ η (tail xs)

  shallow-η : ∀ {n} (xs : Vec A (1 + n)) → xs ≡ head xs ∷ tail xs
  shallow-η (x ∷ xs) = idp

  uncons : ∀ {n} → Vec A (1 + n) → (A × Vec A n)
  uncons (x ∷ xs) = x , xs

  ∷-uncons : ∀ {n} (xs : Vec A (1 + n)) → uncurry _∷_ (uncons xs) ≡ xs
  ∷-uncons (x ∷ xs) = idp

  splitAt′ : ∀ m {n} → Vec A (m + n) → Vec A m × Vec A n
  splitAt′ m xs = case splitAt m xs of λ { (ys , zs , _) → (ys , zs) }

  group : ∀ n k → Vec A (n * k) → Vec (Vec A k) n
  group zero    k v = []
  group (suc n) k v = take k v ∷ group n k (drop k v)

  map2* : ∀ m n (f : Vec A m → Vec A n) → Vec A (2* m) → Vec A (2* n)
  map2* m _ f xs = f (take m xs) ++ f (drop m xs)

  map* : ∀ k {m n}(f : Vec A m → Vec A n) → Vec A (k * m) → Vec A (k * n)
  map* k f xs = concat (map f (group k _ xs))

  take2* : ∀ n → Bit → Vec A (2* n) → Vec A n
  take2* n 0b v = take n v
  take2* n 1b v = drop n v

  ++-decomp : ∀ {m n} {xs zs : Vec A m} {ys ts : Vec A n}
             → (xs ++ ys) ≡ (zs ++ ts) → (xs ≡ zs × ys ≡ ts)
  ++-decomp {zero} {xs = []} {[]} p = idp , p
  ++-decomp {suc m} {xs = x ∷ xs} {z ∷ zs} eq with ++-decomp {m} {xs = xs} {zs} (ap tail eq)
  ... | (q₁ , q₂) = (ap-∷ (ap head eq) q₁) , q₂

  ++-inj₁ : ∀ {m n} {xs ys : Vec A m} {zs ts : Vec A n} → xs ++ zs ≡ ys ++ ts → xs ≡ ys
  ++-inj₁ eq = fst (++-decomp eq)

  ++-inj₂ : ∀ {m n} (xs ys : Vec A m) {zs ts : Vec A n} → xs ++ zs ≡ ys ++ ts → zs ≡ ts
  ++-inj₂ xs ys eq = snd (++-decomp {xs = xs} {zs = ys} eq)

  take-∷ : ∀ {m} n x (xs : Vec A (n + m)) → take (suc n) (x ∷ xs) ≡ x ∷ take n xs
  take-∷ n x xs with splitAt n xs
  take-∷ _ _ ._ | _ , _ , idp = idp

  drop-∷ : ∀ {m} n x (xs : Vec A (n + m)) → drop (suc n) (x ∷ xs) ≡ drop n xs
  drop-∷ n x xs with splitAt n xs
  drop-∷ _ _ ._ | _ , _ , idp = idp

  take-++ : ∀ m {n} (xs : Vec A m) (ys : Vec A n) → take m (xs ++ ys) ≡ xs
  take-++ m xs ys with xs ++ ys | ≡.inspect (_++_ xs) ys
  ... | zs | eq with splitAt m zs
  take-++ m xs₁ ys₁ | .(xs ++ ys) | ≡.[ eq ] | xs , ys , idp = !(++-inj₁ eq)

  drop-++ : ∀ m {n} (xs : Vec A m) (ys : Vec A n) → drop m (xs ++ ys) ≡ ys
  drop-++ m xs ys with xs ++ ys | ≡.inspect (_++_ xs) ys
  ... | zs | eq with splitAt m zs
  drop-++ m xs₁ ys₁ | .(xs ++ ys) | ≡.[ eq ] | xs , ys , idp = !(++-inj₂ xs₁ xs eq)

  take-drop-lem : ∀ m {n} (xs : Vec A (m + n)) → take m xs ++ drop m xs ≡ xs
  take-drop-lem m xs with splitAt m xs
  take-drop-lem m .(ys ++ zs) | ys , zs , idp = idp

  take-them-all : ∀ n (xs : Vec A (n + 0)) → take n xs ++ [] ≡ xs
  take-them-all n xs with splitAt n xs
  take-them-all n .(ys ++ []) | ys , [] , idp = idp

  drop′ : ∀ m {n} → Vec A (m + n) → Vec A n
  drop′ zero    = id
  drop′ (suc m) = drop′ m ∘ tail

  map2*-++ : ∀ {m n}(f : Vec A m → Vec A n) → map2* m n f ∘ uncurry _++_ ≗ uncurry _++_ ∘ ×-map f f
  map2*-++ {m} f (x , y) rewrite take-++ m x y | drop-++ m x y = idp

  drop′-spec : ∀ m {n} → drop′ m {n} ≗ drop m {n}
  drop′-spec zero    _        = idp
  drop′-spec (suc m) (x ∷ xs) = drop′-spec m xs ∙ !(drop-∷ m x xs)

  take′ : ∀ m {n} → Vec A (m + n) → Vec A m
  take′ zero    _  = []
  take′ (suc m) xs = head xs ∷ take′ m (tail xs)

  take′-spec : ∀ m {n} → take′ m {n} ≗ take m {n}
  take′-spec zero    xs       = idp
  take′-spec (suc m) (x ∷ xs) = ap (_∷_ x) (take′-spec m xs) ∙ !(take-∷ m x xs)

  swap : ∀ m {n} → Vec A (m + n) → Vec A (n + m)
  swap m xs = drop m xs ++ take m xs

  swap-++ : ∀ m {n} (xs : Vec A m) (ys : Vec A n) → swap m (xs ++ ys) ≡ ys ++ xs
  swap-++ m xs ys = ap₂ _++_ (drop-++ m xs ys) (take-++ m xs ys)

  rewire : ∀ {i o} → (Fin o → Fin i) → Vec A i → Vec A o
  rewire f v = tabulate (_‼_ v ∘ f)

  take-drop= : ∀ m {n} (xs ys : Vec A (m + n))
                 → take m xs ≡ take m ys
                 → drop m xs ≡ drop m ys
                 → xs ≡ ys
  take-drop= m xs ys take= drop= =
    ! take-drop-lem m xs ∙ ap₂ _++_ take= drop= ∙ take-drop-lem m ys

  rewireTbl : ∀ {i o} → RewireTbl i o → Vec A i → Vec A o
  rewireTbl tbl v = map (_‼_ v) tbl

  onᵢ : ∀ (f : A → A) {n} (i : Fin n) → Vec A n → Vec A n
  onᵢ f zero    (x ∷ xs) = f x ∷ xs
  onᵢ f (suc i) (x ∷ xs) = x ∷ onᵢ f i xs

  ⊛-dist-0↔1 : ∀ {n}(fs : Vec (Endo A) n) xs → (0↔1 fs ⊛ 0↔1 xs) ≡ 0↔1 (fs ⊛ xs)
  ⊛-dist-0↔1 _           []          = idp
  ⊛-dist-0↔1 (_ ∷ [])    (_ ∷ [])    = idp
  ⊛-dist-0↔1 (_ ∷ _ ∷ _) (_ ∷ _ ∷ _) = idp

  map-tail : ∀ {m n} → (Vec A m → Vec A n) → Vec A (suc m) → Vec A (suc n)
  map-tail f (x ∷ xs) = x ∷ f xs

  map-tail-id : ∀ {n} → map-tail id ≗ id {A = Vec A (suc n)}
  map-tail-id (x ∷ xs) = idp

  map-tail∘map-tail : ∀ {m n o}
                        (f : Vec A o → Vec A m)
                        (g : Vec A n → Vec A o)
                      → map-tail f ∘ map-tail g ≗ map-tail (f ∘ g)
  map-tail∘map-tail f g (x ∷ xs) = idp

  map-tail-≗ : ∀ {m n}(f g : Vec A m → Vec A n) → f ≗ g → map-tail f ≗ map-tail g
  map-tail-≗ f g f≗g (x ∷ xs) = ap (_∷_ x) (f≗g xs)

  dup : ∀ {n} → Vec A n → Vec A (n + n)
  dup xs = xs ++ xs

  dup-inj : ∀ {n} → Injective (dup {n})
  dup-inj = ++-inj₁

  rot₁ : ∀ {n} → Vec A n → Vec A n
  rot₁ []       = []
  rot₁ (x ∷ xs) = xs ∷ʳ x

  rot : ∀ {n} → ℕ → Vec A n → Vec A n
  rot zero    xs = xs
  rot (suc n) xs = rot n (rot₁ xs)

  map-∷ʳ : ∀ {n}(f : A → ℕ) x (xs : Vec A n) → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
  map-∷ʳ f x []       = idp
  map-∷ʳ f x (_ ∷ xs) = ap (_∷_ _) (map-∷ʳ f x xs)

  sum-map-rot₁ : ∀ {n}(f : A → ℕ) (xs : Vec A n) → sum (map f (rot₁ xs)) ≡ sum (map f xs)
  sum-map-rot₁ f [] = idp
  sum-map-rot₁ f (x ∷ xs) = ap sum (map-∷ʳ f x xs)
                          ∙ sum-∷ʳ (f x) (map f xs)
                          ∙ ℕ°.+-comm (sum (map f xs)) (f x)

  vec= : ∀ {n}{xs ys : Vec A n} → (∀ i → (xs ‼ i) ≡ (ys ‼ i)) → xs ≡ ys
  vec= {xs = []}     {[]}     f= = idp
  vec= {xs = x ∷ xs} {y ∷ ys} f= = ap-∷ (f= zero) (vec= (f= ∘ suc))

  concat-group : ∀ m n (xs : Vec A (m * n)) → concat (group m n xs) ≡ xs
  concat-group zero    n [] = idp
  concat-group (suc m) n xs rewrite concat-group m n (drop n xs) = take-drop-lem n xs

  group-concat : ∀ {m n}(xss : Vec (Vec A n) m) → group m n (concat xss) ≡ xss
  group-concat [] = idp
  group-concat (xs ∷ xss)
    rewrite take-++ _ xs (concat xss)
          | drop-++ _ xs (concat xss)
          | group-concat xss
          = idp

  -- These are also in the stdlib as Data.Vec.Properties.lookup-morphism
  ‼-replicate : ∀ {n}(i : Fin n)(x : A) → (replicate x ‼ i) ≡ x
  ‼-replicate zero    = λ _ → idp
  ‼-replicate (suc i) = ‼-replicate i

module _ {a b}{A : Type a}{B : Type b} where
  ‼-⊛= : ∀ {n} i {fs : Vec (A → B) n}{xs : Vec A n}{f x}
           (fs= : (fs ‼ i) ≡ f)
           (xs= : (xs ‼ i) ≡ x)
         → (fs ⊛ xs ‼ i) ≡ f x
  ‼-⊛= zero    {f ∷ fs} {x ∷ xs} f= xs= = ap₂ _$_ f= xs=
  ‼-⊛= (suc i) {f ∷ fs} {x ∷ xs} f= xs= = ‼-⊛= i f= xs=

  ‼-⊛ : ∀ {n} i (fs : Vec (A → B) n) (xs : Vec A n) →
          (fs ⊛ xs ‼ i) ≡ (fs ‼ i) (xs ‼ i)
  ‼-⊛ i fs xs = ‼-⊛= i idp idp

  ‼-map= : ∀ {n} i (f : A → B) {xs : Vec A n}{x : A}
             (xs= : (xs ‼ i) ≡ x)
           → (map f xs ‼ i) ≡ f x
  ‼-map= i f = ‼-⊛= i (‼-replicate i f)

  ‼-map : ∀ {n} i (f : A → B) (xs : Vec A n) →
            (map f xs ‼ i) ≡ f (xs ‼ i)
  ‼-map i f xs = ‼-map= i f idp

  ⊛-replicate : ∀ {n}(fs : Vec (A → B) n)(x : A) → (fs ⊛ replicate x) ≡ map (λ f → f x) fs
  ⊛-replicate []       x = idp
  ⊛-replicate (f ∷ fs) x = ap (_∷_ (f x)) (⊛-replicate fs x)

  vuncurry : ∀ {n}(f : A → Vec A n → B) → Vec A (1 + n) → B
  vuncurry f (x ∷ xs) = f x xs

  count-∘ : ∀ {n}(f : A → B)(pred : B → Bool) →
              count {n} (pred ∘ f) ≗ count pred ∘ map f
  count-∘ f pred [] = idp
  count-∘ f pred (x ∷ xs) with pred (f x)
  ... | 1b rewrite count-∘ f pred xs = idp
  ... | 0b rewrite F.inject₁-lemma (countᶠ pred (map f xs))
                 | F.inject₁-lemma (countᶠ (pred ∘ f) xs)
                 | count-∘ f pred xs = idp

module _ {a}{A : Type a} where
  ⊛-take-drop-lem : ∀ m {n o} (xs : Vec (Vec A (m + n)) o)
       → (map _++_ (map (take m) xs) ⊛ map (drop m) xs) ≡ xs
  ⊛-take-drop-lem m xs = vec= λ i →
    ‼-⊛= i (‼-map= i _ (‼-map i _ _)) (‼-map i _ _) ∙
    take-drop-lem m _

  take2*-++ : ∀ n b (xs ys : Vec A n)
              → take2* n b (xs ++ ys) ≡ proj′ (xs , ys) b
  take2*-++ n 0b xs ys = take-++ n xs ys
  take2*-++ n 1b xs ys = drop-++ n xs ys

sum-rot₁ : ∀ {n} (xs : Vec ℕ n) → sum xs ≡ sum (rot₁ xs)
sum-rot₁ []       = idp
sum-rot₁ (x ∷ xs) = ℕ°.+-comm x (sum xs) ∙ !(sum-∷ʳ x xs)

open import Data.Vec public hiding (_⊛_; zipWith; zip; map; applicative; group)
-- -}
-- -}
-- -}
-- -}
