-- NOTE with-K
module Data.Vec.NP where

open import Type hiding (★)
import Level as L
open import Category.Applicative
open import Data.Vec public hiding (_⊛_; zipWith; zip; map; applicative)
open import Data.Nat.NP using (ℕ; suc; zero; _+_; _*_; module ℕ° ; +-interchange ; _≤_)
open import Data.Nat.Properties using (_+-mono_)
open import Data.Fin hiding (_≤_) renaming (_+_ to _+ᶠ_) 
import Data.Fin.Props as F
open import Data.Bool
open import Data.Product hiding (map; zip; swap)
open import Function.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡

module FunVec {a} {A : ★ a} where
    _→ᵛ_ : ℕ → ℕ → ★ a
    i →ᵛ o = Vec A i → Vec A o

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
    tabulate-∘ {zero}  f g = refl
    tabulate-∘ {suc n} f g =
      ≡.cong (_∷_ (f (g zero))) (tabulate-∘ f (g ∘ suc))

    tabulate-ext : ∀ {n a}{A : ★ a}{f g : Fin n → A} → f ≗ g → tabulate f ≡ tabulate g
    tabulate-ext {zero} f≗g = refl
    tabulate-ext {suc n} f≗g rewrite f≗g zero | tabulate-ext (f≗g ∘ suc) = refl

    -- map is functorial.

    map-id : ∀ {a n} {A : ★ a} → map id ≗ id {A = Vec A n}
    map-id []       = refl
    map-id (x ∷ xs) = ≡.cong (_∷_ x) (map-id xs)

    map-∘ : ∀ {a b c n} {A : ★ a} {B : ★ b} {C : ★ c}
            (f : B → C) (g : A → B) →
            _≗_ {A = Vec A n} (map (f ∘ g)) (map f ∘ map g)
    map-∘ f g []       = refl
    map-∘ f g (x ∷ xs) = ≡.cong (_∷_ (f (g x))) (map-∘ f g xs)

    map-ext : ∀ {a b} {A : ★ a} {B : ★ b} {f g : A → B} {n} → f ≗ g → map f ≗ map {n = n} g
    map-ext f≗g [] = refl
    map-ext f≗g (x ∷ xs) rewrite f≗g x | map-ext f≗g xs = refl

open waiting-for-a-fix-in-the-stdlib public

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
count-∘ f pred [] = refl
count-∘ f pred (x ∷ xs) with pred (f x)
... | true rewrite count-∘ f pred xs = refl
... | false rewrite F.inject₁-lemma (countᶠ pred (map f xs))
                  | F.inject₁-lemma (countᶠ (pred ∘ f) xs)
                  | count-∘ f pred xs = refl

count-++ : ∀ {m n a} {A : ★ a} (pred : A → Bool) (xs : Vec A m) (ys : Vec A n)
            → count pred (xs ++ ys) ≡ count pred xs + count pred ys
count-++ pred [] ys = refl
count-++ pred (x ∷ xs) ys with pred x
... | true  rewrite count-++ pred xs ys = refl
... | false rewrite F.inject₁-lemma (countᶠ pred (xs ++ ys))
                  | F.inject₁-lemma (countᶠ pred xs) | count-++ pred xs ys = refl

ext-countᶠ : ∀ {n a} {A : ★ a} {f g : A → Bool} → f ≗ g → (xs : Vec A n) → countᶠ f xs ≡ countᶠ g xs
ext-countᶠ f≗g [] = refl
ext-countᶠ f≗g (x ∷ xs) rewrite ext-countᶠ f≗g xs | f≗g x = refl

filter : ∀ {n a} {A : ★ a} (pred : A → Bool) (xs : Vec A n) → Vec A (count pred xs)
filter pred [] = []
filter pred (x ∷ xs) with pred x
... | true  = x ∷ filter pred xs
... | false rewrite F.inject₁-lemma (countᶠ pred xs) = filter pred xs

η : ∀ {n a} {A : ★ a} → Vec A n → Vec A n
η = tabulate ∘ flip lookup

η′ : ∀ {n a} {A : ★ a} → Vec A n → Vec A n
η′ {zero}  = λ _ → []
η′ {suc n} = λ xs → head xs ∷ η (tail xs)

shallow-η : ∀ {n a} {A : ★ a} (xs : Vec A (1 + n)) → xs ≡ head xs ∷ tail xs
shallow-η (x ∷ xs) = ≡.refl

uncons : ∀ {n a} {A : ★ a} → Vec A (1 + n) → (A × Vec A n)
uncons (x ∷ xs) = x , xs

splitAt′ : ∀ {a} {A : ★ a} m {n} → Vec A (m + n) → Vec A m × Vec A n
splitAt′ m xs = case splitAt m xs of λ { (ys , zs , _) → (ys , zs) }

++-decomp : ∀ {m n a} {A : ★ a} {xs zs : Vec A m} {ys ts : Vec A n}
             → (xs ++ ys) ≡ (zs ++ ts) → (xs ≡ zs × ys ≡ ts)
++-decomp {zero} {xs = []} {[]} p = refl , p
++-decomp {suc m} {xs = x ∷ xs} {z ∷ zs} eq with ++-decomp {m} {xs = xs} {zs} (cong tail eq)
... | (q₁ , q₂) = (cong₂ _∷_ (cong head eq) q₁) , q₂

{-
open import Data.Vec.Equality

module Here {a} {A : ★ a} where
  open Equality (≡.setoid A)
  ≈-splitAt : ∀ {m n} {xs zs : Vec A m} {ys ts : Vec A n}
               → (xs ++ ys) ≈ (zs ++ ts) → (xs ≈ zs × ys ≈ ts)
  ≈-splitAt {zero} {xs = []} {[]} p = []-cong , p
  ≈-splitAt {suc m} {xs = x ∷ xs} {z ∷ zs} (x¹≈x² ∷-cong p) with ≈-splitAt {m} {xs = xs} {zs} p
  ... | (q₁ , q₂) = x¹≈x² ∷-cong q₁ , q₂
-}

++-inj₁ : ∀ {m n} {a} {A : ★ a} (xs ys : Vec A m) {zs ts : Vec A n} → xs ++ zs ≡ ys ++ ts → xs ≡ ys
++-inj₁ xs ys eq = proj₁ (++-decomp eq)

++-inj₂ : ∀ {m n} {a} {A : ★ a} (xs ys : Vec A m) {zs ts : Vec A n} → xs ++ zs ≡ ys ++ ts → zs ≡ ts
++-inj₂ xs ys eq = proj₂ (++-decomp {xs = xs} {ys} eq)

take-∷ : ∀ {m a} {A : ★ a} n x (xs : Vec A (n + m)) → take (suc n) (x ∷ xs) ≡ x ∷ take n xs
take-∷ n x xs with splitAt n xs
take-∷ _ _ ._ | _ , _ , refl = refl

drop-∷ : ∀ {m a} {A : ★ a} n x (xs : Vec A (n + m)) → drop (suc n) (x ∷ xs) ≡ drop n xs
drop-∷ n x xs with splitAt n xs
drop-∷ _ _ ._ | _ , _ , refl = refl

take-++ : ∀ m {n} {a} {A : ★ a} (xs : Vec A m) (ys : Vec A n) → take m (xs ++ ys) ≡ xs
take-++ m xs ys with xs ++ ys | inspect (_++_ xs) ys
... | zs | eq with splitAt m zs
take-++ m xs₁ ys₁ | .(xs ++ ys) | Reveal_is_.[_] eq | xs , ys , refl = sym (++-inj₁ xs₁ xs eq)

drop-++ : ∀ m {n} {a} {A : ★ a} (xs : Vec A m) (ys : Vec A n) → drop m (xs ++ ys) ≡ ys
drop-++ m xs ys with xs ++ ys | inspect (_++_ xs) ys
... | zs | eq with splitAt m zs
drop-++ m xs₁ ys₁ | .(xs ++ ys) | Reveal_is_.[_] eq | xs , ys , refl = sym (++-inj₂ xs₁ xs eq)

take-drop-lem : ∀ m {n} {a} {A : ★ a} (xs : Vec A (m + n)) → take m xs ++ drop m xs ≡ xs
take-drop-lem m xs with splitAt m xs
take-drop-lem m .(ys ++ zs) | ys , zs , refl = refl

take-them-all : ∀ n {a} {A : ★ a} (xs : Vec A (n + 0)) → take n xs ++ [] ≡ xs
take-them-all n xs with splitAt n xs
take-them-all n .(ys ++ []) | ys , [] , refl = refl

drop′ : ∀ {a} {A : ★ a} m {n} → Vec A (m + n) → Vec A n
drop′ zero    = id
drop′ (suc m) = drop′ m ∘ tail

drop′-spec : ∀ {a} {A : ★ a} m {n} → drop′ {A = A} m {n} ≗ drop m {n}
drop′-spec zero xs = refl
drop′-spec (suc m) (x ∷ xs) rewrite drop′-spec m xs | drop-∷ m x xs = refl

take′ : ∀ {a} {A : ★ a} m {n} → Vec A (m + n) → Vec A m
take′ zero    _  = []
take′ (suc m) xs = head xs ∷ take′ m (tail xs)

take′-spec : ∀ {a} {A : ★ a} m {n} → take′ {A = A} m {n} ≗ take m {n}
take′-spec zero xs = refl
take′-spec (suc m) (x ∷ xs) rewrite take′-spec m xs | take-∷ m x xs = refl

swap : ∀ m {n} {a} {A : ★ a} → Vec A (m + n) → Vec A (n + m)
swap m xs = drop m xs ++ take m xs

swap-++ : ∀ m {n} {a} {A : ★ a} (xs : Vec A m) (ys : Vec A n) → swap m (xs ++ ys) ≡ ys ++ xs
swap-++ m xs ys rewrite drop-++ m xs ys | take-++ m xs ys = refl

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
⊛-dist-0↔1 _           []          = refl
⊛-dist-0↔1 (_ ∷ [])    (_ ∷ [])    = refl
⊛-dist-0↔1 (_ ∷ _ ∷ _) (_ ∷ _ ∷ _) = refl

map-tail : ∀ {m n a} {A : ★ a} → (Vec A m → Vec A n) → Vec A (suc m) → Vec A (suc n)
map-tail f (x ∷ xs) = x ∷ f xs

map-tail-id : ∀ {n a} {A : ★ a} → map-tail id ≗ id {A = Vec A (suc n)}
map-tail-id (x ∷ xs) = ≡.refl

map-tail∘map-tail : ∀ {m n o a} {A : ★ a}
                      (f : Vec A o → Vec A m)
                      (g : Vec A n → Vec A o)
                    → map-tail f ∘ map-tail g ≗ map-tail (f ∘ g)
map-tail∘map-tail f g (x ∷ xs) = refl

map-tail-≗ : ∀ {m n a} {A : ★ a} (f g : Vec A m → Vec A n) → f ≗ g → map-tail f ≗ map-tail g
map-tail-≗ f g f≗g (x ∷ xs) rewrite f≗g xs = refl
