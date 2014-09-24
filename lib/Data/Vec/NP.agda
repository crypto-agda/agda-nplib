{-# OPTIONS --copatterns #-}
-- NOTE with-K
module Data.Vec.NP where

open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties
import Algebra.FunctionProperties.Eq
open import Type hiding (★)
import Level as L
open import Category.Applicative
open import Data.Nat.NP using (ℕ; suc; zero; _+_; _*_; module ℕ° ; +-interchange ; _≤_)
open import Data.Nat.Properties using (_+-mono_)
open import Data.Fin hiding (_≤_) renaming (_+_ to _+ᶠ_)
open import Data.Vec using (Vec; []; _∷_; head; tail; replicate; tabulate; foldr; _++_; lookup; splitAt; take; drop; sum; _∷ʳ_)
import Data.Fin.Props as F
open import Data.Bool
open import Data.Product hiding (map; zip; swap) renaming (proj₁ to fst; proj₂ to snd)
open import Function.NP
open import Relation.Binary
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_; ap; idp; _∙_; !_)
import Data.Vec.Equality

module FunVec {a} {A : ★ a} where
    _→ᵛ_ : ℕ → ℕ → ★ a
    i →ᵛ o = Vec A i → Vec A o

ap-∷ : ∀ {a} {A : ★ a} {n}
         {x y : A} {xs ys : Vec A n} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
ap-∷ = ≡.ap₂ _∷_

module waiting-for-a-fix-in-the-stdlib where

    infixl 4 _⊛_

    _⊛_ : ∀ {a b n} {A : ★ a} {B : ★ b} →
          Vec (A → B) n → Vec A n → Vec B n
    _⊛_ {n = zero}  fs xs = []
    _⊛_ {n = suc n} fs xs = head fs (head xs) ∷ (tail fs ⊛ tail xs)

    applicative : ∀ {a n} → RawApplicative (λ (A : ★ a) → Vec A n)
    applicative = record
      { pure = replicate
      ; _⊛_  = _⊛_
      }

    map : ∀ {a b n} {A : ★ a} {B : ★ b} →
          (A → B) → Vec A n → Vec B n
    map f xs = replicate f ⊛ xs

    zipWith : ∀ {a b c n} {A : ★ a} {B : ★ b} {C : ★ c} →
              (A → B → C) → Vec A n → Vec B n → Vec C n
    zipWith _⊕_ xs ys = replicate _⊕_ ⊛ xs ⊛ ys

    zip : ∀ {a b n} {A : ★ a} {B : ★ b} →
          Vec A n → Vec B n → Vec (A × B) n
    zip = zipWith _,_

    tabulate-∘ : ∀ {n a b} {A : ★ a} {B : ★ b}
                 (f : A → B) (g : Fin n → A) →
                 tabulate (f ∘ g) ≡ map f (tabulate g)
    tabulate-∘ {zero}  f g = idp
    tabulate-∘ {suc n} f g = ap (_∷_ _) (tabulate-∘ f (g ∘ suc))

    tabulate-ext : ∀ {n a}{A : ★ a}{f g : Fin n → A} → f ≗ g → tabulate f ≡ tabulate g
    tabulate-ext {zero}  f≗g = idp
    tabulate-ext {suc n} f≗g = ap-∷ (f≗g zero) (tabulate-ext (f≗g ∘ suc))

    -- map is functorial.

    map-id : ∀ {a n} {A : ★ a} → map id ≗ id {A = Vec A n}
    map-id []       = idp
    map-id (x ∷ xs) = ap (_∷_ x) (map-id xs)

    map-∘ : ∀ {a b c n} {A : ★ a} {B : ★ b} {C : ★ c}
            (f : B → C) (g : A → B) →
            _≗_ {A = Vec A n} (map (f ∘ g)) (map f ∘ map g)
    map-∘ f g []       = idp
    map-∘ f g (x ∷ xs) = ap (_∷_ (f (g x))) (map-∘ f g xs)

    map-ext : ∀ {a b} {A : ★ a} {B : ★ b} {f g : A → B} {n} → f ≗ g → map f ≗ map {n = n} g
    map-ext f≗g []       = idp
    map-ext f≗g (x ∷ xs) = ap-∷ (f≗g x) (map-ext f≗g xs)

open waiting-for-a-fix-in-the-stdlib public

module WithSetoid {c ℓ} (S : Setoid c ℓ) where
  A = Setoid.Carrier S
  open Setoid S
  V = Vec A
  module V≈ = Data.Vec.Equality.Equality S
  open Algebra.FunctionProperties
  open V≈ hiding (_≈_)
  _≈ᵛ_ : ∀ {n} → V n → V n → ★ _
  xs ≈ᵛ ys = V≈._≈_ xs ys

  module _ {f : A → A} (f-cong : f Preserves _≈_ ⟶ _≈_) where
    map-cong : ∀ {n} → map {n = n} f Preserves _≈ᵛ_ ⟶ _≈ᵛ_
    map-cong []-cong = []-cong
    map-cong (x≈y ∷-cong xs≈ys) = f-cong x≈y ∷-cong map-cong xs≈ys

  module _ {f g : A → A → A}
                 (f-g : ∀ x y z → f (g x y) z ≈ f x (g y z)) where
    zipWith-assoc :
      ∀ {n} (xs ys zs : Vec A n) →
      zipWith f (zipWith g xs ys) zs ≈ᵛ zipWith f xs (zipWith g ys zs)
    zipWith-assoc [] [] [] = []-cong
    zipWith-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs)
       = f-g x y z ∷-cong (zipWith-assoc xs ys zs)

  module _ {f : A → A → A} (f-cong : f Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_) where
    zipWith-cong : ∀ {n} → zipWith {n = n} f Preserves₂ _≈ᵛ_ ⟶ _≈ᵛ_ ⟶ _≈ᵛ_
    zipWith-cong []-cong []-cong = []-cong
    zipWith-cong (x≈y ∷-cong xs≈ys) (z≈t ∷-cong zs≈ts) = f-cong x≈y z≈t ∷-cong zipWith-cong xs≈ys zs≈ts

  module _ {_∙_ : A → A → A} {ε : A} (∙-id-left : LeftIdentity _≈_ ε _∙_) where
    zipWith-id-left : ∀ {n} → LeftIdentity _≈ᵛ_ (replicate ε) (zipWith {n = n} _∙_)
    zipWith-id-left [] = []-cong
    zipWith-id-left (x ∷ xs) = ∙-id-left x ∷-cong zipWith-id-left xs

  module _ {_∙_ : A → A → A} {ε : A} (∙-id-right : RightIdentity _≈_ ε _∙_) where
    zipWith-id-right : ∀ {n} → RightIdentity _≈ᵛ_ (replicate ε) (zipWith {n = n} _∙_)
    zipWith-id-right [] = []-cong
    zipWith-id-right (x ∷ xs) = ∙-id-right x ∷-cong zipWith-id-right xs

  module _ {_∙_ : A → A → A} (∙-comm : Commutative _≈_ _∙_) where
    zipWith-comm : ∀ {n} → Commutative _≈ᵛ_ (zipWith {n = n} _∙_)
    zipWith-comm [] [] = []-cong
    zipWith-comm (x ∷ xs) (y ∷ ys) = ∙-comm x y ∷-cong zipWith-comm xs ys

  module _ {ε : A} {_⁻¹ : A → A} {_∙_ : A → A → A}
                 (inverse : LeftInverse _≈_ ε _⁻¹ _∙_) where
     zipWith-left-inverse : ∀ {n} → LeftInverse _≈ᵛ_ (replicate ε) (map _⁻¹) (zipWith {n = n} _∙_)
     zipWith-left-inverse [] = []-cong
     zipWith-left-inverse (x ∷ xs) = inverse x ∷-cong zipWith-left-inverse xs

  module _ {ε : A} {_⁻¹ : A → A} {_∙_ : A → A → A}
                 (inverse : RightInverse _≈_ ε _⁻¹ _∙_) where
     zipWith-right-inverse : ∀ {n} → RightInverse _≈ᵛ_ (replicate ε) (map _⁻¹) (zipWith {n = n} _∙_)
     zipWith-right-inverse [] = []-cong
     zipWith-right-inverse (x ∷ xs) = inverse x ∷-cong zipWith-right-inverse xs

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

-- Trying to get rid of the foldl in the definition of reverse and
-- without using equations on natural numbers.
-- In the end that's not very convincing.
module Alternative-Reverse where
    rev-+ : ℕ → ℕ → ℕ
    rev-+ zero    = id
    rev-+ (suc x) = rev-+ x ∘ suc

    rev-app : ∀ {a} {A : ★ a} {m n} →
              Vec A n → Vec A m → Vec A (rev-+ n m)
    rev-app []       = id
    rev-app (x ∷ xs) = rev-app xs ∘ _∷_ x

    rev-aux : ∀ {a} {A : ★ a} {m} n →
              Vec A (rev-+ n zero) →
              (∀ {m} → A → Vec A (rev-+ n m) → Vec A (rev-+ n (suc m))) →
              Vec A m → Vec A (rev-+ n m)
    rev-aux m acc op []       = acc
    rev-aux m acc op (x ∷ xs) = rev-aux (suc m) (op x acc) op xs

    alt-reverse : ∀ {a n} {A : ★ a} → Vec A n → Vec A n
    alt-reverse = rev-aux 0 [] _∷_

vuncurry : ∀ {n a b} {A : ★ a} {B : ★ b} (f : A → Vec A n → B) → Vec A (1 + n) → B
vuncurry f (x ∷ xs) = f x xs

countᶠ : ∀ {n a} {A : ★ a} → (A → Bool) → Vec A n → Fin (suc n)
countᶠ pred = foldr (Fin ∘ suc) (λ x → if pred x then suc else inject₁) zero

count : ∀ {n a} {A : ★ a} → (A → Bool) → Vec A n → ℕ
count pred = toℕ ∘ countᶠ pred

count-∘ : ∀ {n a b} {A : ★ a} {B : ★ b} (f : A → B) (pred : B → Bool) →
            count {n} (pred ∘ f) ≗ count pred ∘ map f
count-∘ f pred [] = idp
count-∘ f pred (x ∷ xs) with pred (f x)
... | true rewrite count-∘ f pred xs = idp
... | false rewrite F.inject₁-lemma (countᶠ pred (map f xs))
                  | F.inject₁-lemma (countᶠ (pred ∘ f) xs)
                  | count-∘ f pred xs = idp

count-++ : ∀ {m n a} {A : ★ a} (pred : A → Bool) (xs : Vec A m) (ys : Vec A n)
            → count pred (xs ++ ys) ≡ count pred xs + count pred ys
count-++ pred [] ys = idp
count-++ pred (x ∷ xs) ys with pred x
... | true  rewrite count-++ pred xs ys = idp
... | false rewrite F.inject₁-lemma (countᶠ pred (xs ++ ys))
                  | F.inject₁-lemma (countᶠ pred xs) | count-++ pred xs ys = idp

ext-countᶠ : ∀ {n a} {A : ★ a} {f g : A → Bool} → f ≗ g → (xs : Vec A n) → countᶠ f xs ≡ countᶠ g xs
ext-countᶠ f≗g [] = idp
ext-countᶠ f≗g (x ∷ xs) rewrite ext-countᶠ f≗g xs | f≗g x = idp

filter : ∀ {n a} {A : ★ a} (pred : A → Bool) (xs : Vec A n) → Vec A (count pred xs)
filter pred [] = []
filter pred (x ∷ xs) with pred x
... | true  = x ∷ filter pred xs
... | false rewrite F.inject₁-lemma (countᶠ pred xs) = filter pred xs

transpose : ∀ {m n a} {A : ★ a} → Vec (Vec A m) n → Vec (Vec A n) m
transpose [] = replicate []
transpose (xs ∷ xss) = zipWith _∷_ xs (transpose xss)

vap : ∀ {m a b} {A : ★ a} {B : ★ b} (f : Vec A m → B)
        → ∀ {n} → Vec (Vec A n) m → Vec B n
vap f = map f ∘ transpose

η : ∀ {n a} {A : ★ a} → Vec A n → Vec A n
η = tabulate ∘ flip lookup

η′ : ∀ {n a} {A : ★ a} → Vec A n → Vec A n
η′ {zero}  = λ _ → []
η′ {suc n} = λ xs → head xs ∷ η (tail xs)

shallow-η : ∀ {n a} {A : ★ a} (xs : Vec A (1 + n)) → xs ≡ head xs ∷ tail xs
shallow-η (x ∷ xs) = idp

uncons : ∀ {n a} {A : ★ a} → Vec A (1 + n) → (A × Vec A n)
uncons (x ∷ xs) = x , xs

∷-uncons : ∀ {n a} {A : ★ a} (xs : Vec A (1 + n)) → uncurry _∷_ (uncons xs) ≡ xs
∷-uncons (x ∷ xs) = idp

splitAt′ : ∀ {a} {A : ★ a} m {n} → Vec A (m + n) → Vec A m × Vec A n
splitAt′ m xs = case splitAt m xs of λ { (ys , zs , _) → (ys , zs) }

++-decomp : ∀ {m n a} {A : ★ a} {xs zs : Vec A m} {ys ts : Vec A n}
             → (xs ++ ys) ≡ (zs ++ ts) → (xs ≡ zs × ys ≡ ts)
++-decomp {zero} {xs = []} {[]} p = idp , p
++-decomp {suc m} {xs = x ∷ xs} {z ∷ zs} eq with ++-decomp {m} {xs = xs} {zs} (ap tail eq)
... | (q₁ , q₂) = (ap-∷ (ap head eq) q₁) , q₂

{-

module Here {a} {A : ★ a} where
  open Data.Vec.Equality.Equality (≡.setoid A)
  ≈-splitAt : ∀ {m n} {xs zs : Vec A m} {ys ts : Vec A n}
               → (xs ++ ys) ≈ (zs ++ ts) → (xs ≈ zs × ys ≈ ts)
  ≈-splitAt {zero} {xs = []} {[]} p = []-cong , p
  ≈-splitAt {suc m} {xs = x ∷ xs} {z ∷ zs} (x¹≈x² ∷-cong p) with ≈-splitAt {m} {xs = xs} {zs} p
  ... | (q₁ , q₂) = x¹≈x² ∷-cong q₁ , q₂
-}

++-inj₁ : ∀ {m n} {a} {A : ★ a} {xs ys : Vec A m} {zs ts : Vec A n} → xs ++ zs ≡ ys ++ ts → xs ≡ ys
++-inj₁ eq = fst (++-decomp eq)

++-inj₂ : ∀ {m n} {a} {A : ★ a} (xs ys : Vec A m) {zs ts : Vec A n} → xs ++ zs ≡ ys ++ ts → zs ≡ ts
++-inj₂ xs ys eq = snd (++-decomp {xs = xs} {zs = ys} eq)

take-∷ : ∀ {m a} {A : ★ a} n x (xs : Vec A (n + m)) → take (suc n) (x ∷ xs) ≡ x ∷ take n xs
take-∷ n x xs with splitAt n xs
take-∷ _ _ ._ | _ , _ , ≡.refl = ≡.refl

drop-∷ : ∀ {m a} {A : ★ a} n x (xs : Vec A (n + m)) → drop (suc n) (x ∷ xs) ≡ drop n xs
drop-∷ n x xs with splitAt n xs
drop-∷ _ _ ._ | _ , _ , ≡.refl = ≡.refl

take-++ : ∀ m {n} {a} {A : ★ a} (xs : Vec A m) (ys : Vec A n) → take m (xs ++ ys) ≡ xs
take-++ m xs ys with xs ++ ys | ≡.inspect (_++_ xs) ys
... | zs | eq with splitAt m zs
take-++ m xs₁ ys₁ | .(xs ++ ys) | ≡.[ eq ] | xs , ys , ≡.refl = !(++-inj₁ eq)

drop-++ : ∀ m {n} {a} {A : ★ a} (xs : Vec A m) (ys : Vec A n) → drop m (xs ++ ys) ≡ ys
drop-++ m xs ys with xs ++ ys | ≡.inspect (_++_ xs) ys
... | zs | eq with splitAt m zs
drop-++ m xs₁ ys₁ | .(xs ++ ys) | ≡.[ eq ] | xs , ys , ≡.refl = !(++-inj₂ xs₁ xs eq)

take-drop-lem : ∀ m {n} {a} {A : ★ a} (xs : Vec A (m + n)) → take m xs ++ drop m xs ≡ xs
take-drop-lem m xs with splitAt m xs
take-drop-lem m .(ys ++ zs) | ys , zs , ≡.refl = ≡.refl

take-them-all : ∀ n {a} {A : ★ a} (xs : Vec A (n + 0)) → take n xs ++ [] ≡ xs
take-them-all n xs with splitAt n xs
take-them-all n .(ys ++ []) | ys , [] , ≡.refl = ≡.refl

drop′ : ∀ {a} {A : ★ a} m {n} → Vec A (m + n) → Vec A n
drop′ zero    = id
drop′ (suc m) = drop′ m ∘ tail

drop′-spec : ∀ {a} {A : ★ a} m {n} → drop′ {A = A} m {n} ≗ drop m {n}
drop′-spec zero    _        = idp
drop′-spec (suc m) (x ∷ xs) = drop′-spec m xs ∙ !(drop-∷ m x xs)

take′ : ∀ {a} {A : ★ a} m {n} → Vec A (m + n) → Vec A m
take′ zero    _  = []
take′ (suc m) xs = head xs ∷ take′ m (tail xs)

take′-spec : ∀ {a} {A : ★ a} m {n} → take′ {A = A} m {n} ≗ take m {n}
take′-spec zero    xs       = idp
take′-spec (suc m) (x ∷ xs) = ap (_∷_ x) (take′-spec m xs) ∙ !(take-∷ m x xs)

swap : ∀ m {n} {a} {A : ★ a} → Vec A (m + n) → Vec A (n + m)
swap m xs = drop m xs ++ take m xs

swap-++ : ∀ m {n} {a} {A : ★ a} (xs : Vec A m) (ys : Vec A n) → swap m (xs ++ ys) ≡ ys ++ xs
swap-++ m xs ys = ≡.ap₂ _++_ (drop-++ m xs ys) (take-++ m xs ys)

rewire : ∀ {a i o} {A : ★ a} → (Fin o → Fin i) → Vec A i → Vec A o
rewire f v = tabulate (flip lookup v ∘ f)

RewireTbl : (i o : ℕ) → ★₀
RewireTbl i o = Vec (Fin i) o

rewireTbl : ∀ {a i o} {A : ★ a} → RewireTbl i o → Vec A i → Vec A o
rewireTbl tbl v = map (flip lookup v) tbl

onᵢ : ∀ {a} {A : ★ a} (f : A → A) {n} (i : Fin n) → Vec A n → Vec A n
onᵢ f zero    (x ∷ xs) = f x ∷ xs
onᵢ f (suc i) (x ∷ xs) = x ∷ onᵢ f i xs

-- Exchange elements at positions 0 and 1 of a given vector
-- (this only apply if the vector is long enough).
0↔1 : ∀ {n a} {A : ★ a} → Vec A n → Vec A n
0↔1 (x₀ ∷ x₁ ∷ xs) = x₁ ∷ x₀ ∷ xs
0↔1 xs = xs

⊛-dist-0↔1 : ∀ {n a} {A : ★ a} (fs : Vec (Endo A) n) xs → 0↔1 fs ⊛ 0↔1 xs ≡ 0↔1 (fs ⊛ xs)
⊛-dist-0↔1 _           []          = idp
⊛-dist-0↔1 (_ ∷ [])    (_ ∷ [])    = idp
⊛-dist-0↔1 (_ ∷ _ ∷ _) (_ ∷ _ ∷ _) = idp

map-tail : ∀ {m n a} {A : ★ a} → (Vec A m → Vec A n) → Vec A (suc m) → Vec A (suc n)
map-tail f (x ∷ xs) = x ∷ f xs

map-tail-id : ∀ {n a} {A : ★ a} → map-tail id ≗ id {A = Vec A (suc n)}
map-tail-id (x ∷ xs) = idp

map-tail∘map-tail : ∀ {m n o a} {A : ★ a}
                      (f : Vec A o → Vec A m)
                      (g : Vec A n → Vec A o)
                    → map-tail f ∘ map-tail g ≗ map-tail (f ∘ g)
map-tail∘map-tail f g (x ∷ xs) = idp

map-tail-≗ : ∀ {m n a} {A : ★ a} (f g : Vec A m → Vec A n) → f ≗ g → map-tail f ≗ map-tail g
map-tail-≗ f g f≗g (x ∷ xs) = ap (_∷_ x) (f≗g xs)

sum-∷ʳ : ∀ {n} x (xs : Vec ℕ n) → sum (xs ∷ʳ x) ≡ sum xs + x
sum-∷ʳ x []        = ℕ°.+-comm x 0
sum-∷ʳ x (x₁ ∷ xs) = ap (_+_ x₁) (sum-∷ʳ x xs) ∙ !(ℕ°.+-assoc x₁ (sum xs) x)

rot₁ : ∀ {n a} {A : ★ a} → Vec A n → Vec A n
rot₁ []       = []
rot₁ (x ∷ xs) = xs ∷ʳ x

rot : ∀ {n a} {A : ★ a} → ℕ → Vec A n → Vec A n
rot zero    xs = xs
rot (suc n) xs = rot n (rot₁ xs)

sum-distribˡ : ∀ {A : ★₀} {n} f k (xs : Vec A n) → sum (map (λ x → k * f x) xs) ≡ k * sum (map f xs)
sum-distribˡ f k [] = ℕ°.*-comm 0 k
sum-distribˡ f k (x ∷ xs) rewrite sum-distribˡ f k xs = !(fst ℕ°.distrib k _ _)

sum-linear : ∀ {A : ★₀} {n} f g (xs : Vec A n) → sum (map (λ x → f x + g x) xs) ≡ sum (map f xs) + sum (map g xs)
sum-linear f g [] = idp
sum-linear f g (x ∷ xs) rewrite sum-linear f g xs = +-interchange (f x) (g x) (sum (map f xs)) (sum (map g xs))

sum-mono : ∀ {A : ★₀} {n f g} (mono : ∀ x → f x ≤ g x)(xs : Vec A n) → sum (map f xs) ≤ sum (map g xs)
sum-mono f≤°g [] = Data.Nat.NP.z≤n
sum-mono f≤°g (x ∷ xs) = f≤°g x +-mono sum-mono f≤°g xs

sum-rot₁ : ∀ {n} (xs : Vec ℕ n) → sum xs ≡ sum (rot₁ xs)
sum-rot₁ []       = idp
sum-rot₁ (x ∷ xs) = ℕ°.+-comm x (sum xs) ∙ !(sum-∷ʳ x xs)

map-∷ʳ : ∀ {n a} {A : ★ a} (f : A → ℕ) x (xs : Vec A n) → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
map-∷ʳ f x []       = idp
map-∷ʳ f x (_ ∷ xs) = ap (_∷_ _) (map-∷ʳ f x xs)

sum-map-rot₁ : ∀ {n a} {A : ★ a} (f : A → ℕ) (xs : Vec A n) → sum (map f (rot₁ xs)) ≡ sum (map f xs)
sum-map-rot₁ f [] = idp
sum-map-rot₁ f (x ∷ xs) = ap sum (map-∷ʳ f x xs)
                        ∙ sum-∷ʳ (f x) (map f xs)
                        ∙ ℕ°.+-comm (sum (map f xs)) (f x)

open import Data.Vec public hiding (_⊛_; zipWith; zip; map; applicative)
open Algebra.FunctionProperties.Eq

module _ {a} {A : ★ a} where
    dup : ∀ {n} → Vec A n → Vec A (n + n)
    dup xs = xs ++ xs

    dup-inj : ∀ {n} → Injective (dup {n})
    dup-inj = ++-inj₁
-- -}
-- -}
-- -}
-- -}
