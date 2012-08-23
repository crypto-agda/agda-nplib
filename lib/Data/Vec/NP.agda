module Data.Vec.NP where

import Level as L
open import Category.Applicative
open import Data.Vec public hiding (_⊛_; zipWith; zip; map; applicative)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin renaming (_+_ to _+ᶠ_)
import Data.Fin.Props as F
open import Data.Bool
open import Data.Product hiding (map; zip; swap)
open import Function.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡
open import Function.Bijection.SyntaxKit

module waiting-for-a-fix-in-the-stdlib where

    infixl 4 _⊛_

    _⊛_ : ∀ {a b n} {A : Set a} {B : Set b} →
          Vec (A → B) n → Vec A n → Vec B n
    _⊛_ {n = zero}  fs xs = []
    _⊛_ {n = suc n} fs xs = head fs (head xs) ∷ (tail fs ⊛ tail xs)

    applicative : ∀ {a n} → RawApplicative (λ (A : Set a) → Vec A n)
    applicative = record
      { pure = replicate
      ; _⊛_  = _⊛_
      }

    map : ∀ {a b n} {A : Set a} {B : Set b} →
          (A → B) → Vec A n → Vec B n
    map f xs = replicate f ⊛ xs

    zipWith : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c} →
              (A → B → C) → Vec A n → Vec B n → Vec C n
    zipWith _⊕_ xs ys = replicate _⊕_ ⊛ xs ⊛ ys

    zip : ∀ {a b n} {A : Set a} {B : Set b} →
          Vec A n → Vec B n → Vec (A × B) n
    zip = zipWith _,_

    tabulate-∘ : ∀ {n a b} {A : Set a} {B : Set b}
                 (f : A → B) (g : Fin n → A) →
                 tabulate (f ∘ g) ≡ map f (tabulate g)
    tabulate-∘ {zero}  f g = refl
    tabulate-∘ {suc n} f g =
      ≡.cong (_∷_ (f (g zero))) (tabulate-∘ f (g ∘ suc))

open waiting-for-a-fix-in-the-stdlib public

-- Trying to get rid of the foldl in the definition of reverse and
-- without using equations on natural numbers.
-- In the end that's not very convincing.
module Alternative-Reverse where
    rev-+ : ℕ → ℕ → ℕ
    rev-+ zero    = id
    rev-+ (suc x) = rev-+ x ∘ suc

    rev-app : ∀ {a} {A : Set a} {m n} →
              Vec A n → Vec A m → Vec A (rev-+ n m)
    rev-app []       = id
    rev-app (x ∷ xs) = rev-app xs ∘ _∷_ x

    rev-aux : ∀ {a} {A : Set a} {m} n →
              Vec A (rev-+ n zero) →
              (∀ {m} → A → Vec A (rev-+ n m) → Vec A (rev-+ n (suc m))) →
              Vec A m → Vec A (rev-+ n m)
    rev-aux m acc op []       = acc
    rev-aux m acc op (x ∷ xs) = rev-aux (suc m) (op x acc) op xs

    alt-reverse : ∀ {a n} {A : Set a} → Vec A n → Vec A n
    alt-reverse = rev-aux 0 [] _∷_

vuncurry : ∀ {n a b} {A : Set a} {B : Set b} (f : A → Vec A n → B) → Vec A (1 + n) → B
vuncurry f (x ∷ xs) = f x xs

countᶠ : ∀ {n a} {A : Set a} → (A → Bool) → Vec A n → Fin (suc n)
countᶠ pred = foldr (Fin ∘ suc) (λ x → if pred x then suc else inject₁) zero

count : ∀ {n a} {A : Set a} → (A → Bool) → Vec A n → ℕ
count pred = toℕ ∘ countᶠ pred

count-∘ : ∀ {n a b} {A : Set a} {B : Set b} (f : A → B) (pred : B → Bool) →
            count {n} (pred ∘ f) ≗ count pred ∘ map f
count-∘ f pred [] = refl
count-∘ f pred (x ∷ xs) with pred (f x)
... | true rewrite count-∘ f pred xs = refl
... | false rewrite F.inject₁-lemma (countᶠ pred (map f xs))
                  | F.inject₁-lemma (countᶠ (pred ∘ f) xs)
                  | count-∘ f pred xs = refl

count-++ : ∀ {m n a} {A : Set a} (pred : A → Bool) (xs : Vec A m) (ys : Vec A n)
            → count pred (xs ++ ys) ≡ count pred xs + count pred ys
count-++ pred [] ys = refl
count-++ pred (x ∷ xs) ys with pred x
... | true  rewrite count-++ pred xs ys = refl
... | false rewrite F.inject₁-lemma (countᶠ pred (xs ++ ys))
                  | F.inject₁-lemma (countᶠ pred xs) | count-++ pred xs ys = refl

ext-countᶠ : ∀ {n a} {A : Set a} {f g : A → Bool} → f ≗ g → (xs : Vec A n) → countᶠ f xs ≡ countᶠ g xs
ext-countᶠ f≗g [] = refl
ext-countᶠ f≗g (x ∷ xs) rewrite ext-countᶠ f≗g xs | f≗g x = refl

filter : ∀ {n a} {A : Set a} (pred : A → Bool) (xs : Vec A n) → Vec A (count pred xs)
filter pred [] = []
filter pred (x ∷ xs) with pred x
... | true  = x ∷ filter pred xs
... | false rewrite F.inject₁-lemma (countᶠ pred xs) = filter pred xs

η : ∀ {n a} {A : Set a} → Vec A n → Vec A n
η = tabulate ∘ flip lookup

η′ : ∀ {n a} {A : Set a} → Vec A n → Vec A n
η′ {zero}  = λ _ → []
η′ {suc n} = λ xs → head xs ∷ η (tail xs)

shallow-η : ∀ {n a} {A : Set a} (xs : Vec A (1 + n)) → xs ≡ head xs ∷ tail xs
shallow-η (x ∷ xs) = ≡.refl

uncons : ∀ {n a} {A : Set a} → Vec A (1 + n) → (A × Vec A n)
uncons (x ∷ xs) = x , xs

splitAt′ : ∀ {a} {A : Set a} m {n} → Vec A (m + n) → Vec A m × Vec A n
splitAt′ m xs = case splitAt m xs of λ { (ys , zs , _) → (ys , zs) }

++-decomp : ∀ {m n a} {A : Set a} {xs zs : Vec A m} {ys ts : Vec A n}
             → (xs ++ ys) ≡ (zs ++ ts) → (xs ≡ zs × ys ≡ ts)
++-decomp {zero} {xs = []} {[]} p = refl , p
++-decomp {suc m} {xs = x ∷ xs} {z ∷ zs} eq with ++-decomp {m} {xs = xs} {zs} (cong tail eq)
... | (q₁ , q₂) = (cong₂ _∷_ (cong head eq) q₁) , q₂

{-
open import Data.Vec.Equality

module Here {a} {A : Set a} where
  open Equality (≡.setoid A)
  ≈-splitAt : ∀ {m n} {xs zs : Vec A m} {ys ts : Vec A n}
               → (xs ++ ys) ≈ (zs ++ ts) → (xs ≈ zs × ys ≈ ts)
  ≈-splitAt {zero} {xs = []} {[]} p = []-cong , p
  ≈-splitAt {suc m} {xs = x ∷ xs} {z ∷ zs} (x¹≈x² ∷-cong p) with ≈-splitAt {m} {xs = xs} {zs} p
  ... | (q₁ , q₂) = x¹≈x² ∷-cong q₁ , q₂
-}

++-inj₁ : ∀ {m n} {a} {A : Set a} (xs ys : Vec A m) {zs ts : Vec A n} → xs ++ zs ≡ ys ++ ts → xs ≡ ys
++-inj₁ xs ys eq = proj₁ (++-decomp eq)

++-inj₂ : ∀ {m n} {a} {A : Set a} (xs ys : Vec A m) {zs ts : Vec A n} → xs ++ zs ≡ ys ++ ts → zs ≡ ts
++-inj₂ xs ys eq = proj₂ (++-decomp {xs = xs} {ys} eq)

take-∷ : ∀ {m a} {A : Set a} n x (xs : Vec A (n + m)) → take (suc n) (x ∷ xs) ≡ x ∷ take n xs
take-∷ n x xs with splitAt n xs
take-∷ _ _ ._ | _ , _ , refl = refl

drop-∷ : ∀ {m a} {A : Set a} n x (xs : Vec A (n + m)) → drop (suc n) (x ∷ xs) ≡ drop n xs
drop-∷ n x xs with splitAt n xs
drop-∷ _ _ ._ | _ , _ , refl = refl

take-++ : ∀ m {n} {a} {A : Set a} (xs : Vec A m) (ys : Vec A n) → take m (xs ++ ys) ≡ xs
take-++ m xs ys with xs ++ ys | inspect (_++_ xs) ys
... | zs | eq with splitAt m zs
take-++ m xs₁ ys₁ | .(xs ++ ys) | Reveal_is_.[_] eq | xs , ys , refl = sym (++-inj₁ xs₁ xs eq)

drop-++ : ∀ m {n} {a} {A : Set a} (xs : Vec A m) (ys : Vec A n) → drop m (xs ++ ys) ≡ ys
drop-++ m xs ys with xs ++ ys | inspect (_++_ xs) ys
... | zs | eq with splitAt m zs
drop-++ m xs₁ ys₁ | .(xs ++ ys) | Reveal_is_.[_] eq | xs , ys , refl = sym (++-inj₂ xs₁ xs eq)

take-drop-lem : ∀ m {n} {a} {A : Set a} (xs : Vec A (m + n)) → take m xs ++ drop m xs ≡ xs
take-drop-lem m xs with splitAt m xs
take-drop-lem m .(ys ++ zs) | ys , zs , refl = refl

take-them-all : ∀ n {a} {A : Set a} (xs : Vec A (n + 0)) → take n xs ++ [] ≡ xs
take-them-all n xs with splitAt n xs
take-them-all n .(ys ++ []) | ys , [] , refl = refl

drop′ : ∀ {a} {A : Set a} m {n} → Vec A (m + n) → Vec A n
drop′ zero    = id
drop′ (suc m) = drop′ m ∘ tail

drop′-spec : ∀ {a} {A : Set a} m {n} → drop′ {A = A} m {n} ≗ drop m {n}
drop′-spec zero xs = refl
drop′-spec (suc m) (x ∷ xs) rewrite drop′-spec m xs | drop-∷ m x xs = refl

take′ : ∀ {a} {A : Set a} m {n} → Vec A (m + n) → Vec A m
take′ zero    _  = []
take′ (suc m) xs = head xs ∷ take′ m (tail xs)

take′-spec : ∀ {a} {A : Set a} m {n} → take′ {A = A} m {n} ≗ take m {n}
take′-spec zero xs = refl
take′-spec (suc m) (x ∷ xs) rewrite take′-spec m xs | take-∷ m x xs = refl

swap : ∀ m {n} {a} {A : Set a} → Vec A (m + n) → Vec A (n + m)
swap m xs = drop m xs ++ take m xs

swap-++ : ∀ m {n} {a} {A : Set a} (xs : Vec A m) (ys : Vec A n) → swap m (xs ++ ys) ≡ ys ++ xs
swap-++ m xs ys rewrite drop-++ m xs ys | take-++ m xs ys = refl

rewire : ∀ {a i o} {A : Set a} → (Fin o → Fin i) → Vec A i → Vec A o
rewire f v = tabulate (flip lookup v ∘ f)

RewireTbl : (i o : ℕ) → Set
RewireTbl i o = Vec (Fin i) o

rewireTbl : ∀ {a i o} {A : Set a} → RewireTbl i o → Vec A i → Vec A o
rewireTbl tbl v = map (flip lookup v) tbl

onᵢ : ∀ {a} {A : Set a} (f : A → A) {n} (i : Fin n) → Vec A n → Vec A n
onᵢ f zero    (x ∷ xs) = f x ∷ xs
onᵢ f (suc i) (x ∷ xs) = x ∷ onᵢ f i xs

-- Exchange elements at positions 0 and 1 of a given vector
-- (this only apply if the vector is long enough).
0↔1 : ∀ {n a} {A : Set a} → Vec A n → Vec A n
0↔1 (x₀ ∷ x₁ ∷ xs) = x₁ ∷ x₀ ∷ xs
0↔1 xs = xs

⊛-dist-0↔1 : ∀ {n a} {A : Set a} (fs : Vec (Endo A) n) xs → 0↔1 fs ⊛ 0↔1 xs ≡ 0↔1 (fs ⊛ xs)
⊛-dist-0↔1 _           []          = refl
⊛-dist-0↔1 (_ ∷ [])    (_ ∷ [])    = refl
⊛-dist-0↔1 (_ ∷ _ ∷ _) (_ ∷ _ ∷ _) = refl

map-tail : ∀ {m n a} {A : Set a} → (Vec A m → Vec A n) → Vec A (suc m) → Vec A (suc n)
map-tail f (x ∷ xs) = x ∷ f xs

map-tail-id : ∀ {n a} {A : Set a} → map-tail id ≗ id {A = Vec A (suc n)}
map-tail-id (x ∷ xs) = ≡.refl

map-tail∘map-tail : ∀ {m n o a} {A : Set a}
                      (f : Vec A o → Vec A m)
                      (g : Vec A n → Vec A o)
                    → map-tail f ∘ map-tail g ≗ map-tail (f ∘ g)
map-tail∘map-tail f g (x ∷ xs) = refl

map-tail-≗ : ∀ {m n a} {A : Set a} (f g : Vec A m → Vec A n) → f ≗ g → map-tail f ≗ map-tail g
map-tail-≗ f g f≗g (x ∷ xs) rewrite f≗g xs = refl

-- ⟨0↔1+ i ⟩: Exchange elements at position 0 and 1+i.
⟨0↔1+_⟩ : ∀ {n} (i : Fin n) {a} {A : Set a} → Vec A (1 + n) → Vec A (1 + n)
⟨0↔1+ zero  ⟩ = 0↔1
⟨0↔1+ suc i ⟩ = 0↔1 ∘ (map-tail ⟨0↔1+ i ⟩) ∘ 0↔1
  {- 0   1   2 3 ... i 1+i ... n
     1   0   2 3 ... i 1+i ... n
     1   1+i 2 3 ... i 0   ... n

     1+i 1   2 3 ... i 0   ... n
   -}

-- ⟨0↔ i ⟩: Exchange elements at position 0 and i.
⟨0↔_⟩ : ∀ {n} (i : Fin n) {a} {A : Set a} → Vec A n → Vec A n
⟨0↔ zero  ⟩ = id
⟨0↔ suc i ⟩ = ⟨0↔1+ i ⟩

⟨0↔zero⟩ : ∀ {n a} {A : Set a} → ⟨0↔ zero ⟩ ≗ id {A = Vec A (suc n)}
⟨0↔zero⟩ _ = ≡.refl

_² : ∀ {a} {A : Set a} → Endo (Endo A)
f ² = f ∘ f

module ⟨↔⟩ {a} (A : Set a) where

    ⟨_↔_⟩ : ∀ {n} (i j : Fin n) → Vec A n → Vec A n
    ⟨ zero  ↔ j     ⟩ = ⟨0↔ j ⟩
    ⟨ i     ↔ zero  ⟩ = ⟨0↔ i ⟩
    ⟨ suc i ↔ suc j ⟩ = map-tail ⟨ i ↔ j ⟩
-- ⟨ # 0 ↔ # 1 ⟩

    comm : ∀ {n} (i j : Fin n) → ⟨ i ↔ j ⟩ ≗ ⟨ j ↔ i ⟩
    comm zero    zero    _ = ≡.refl
    comm zero    (suc _) _ = ≡.refl
    comm (suc _) zero    _ = ≡.refl
    comm (suc i) (suc j) (x ∷ xs) rewrite comm i j xs = ≡.refl

    0↔1²-cancel : ∀ {n} → 0↔1 ² ≗ id {A = Vec A n}
    0↔1²-cancel [] = refl
    0↔1²-cancel (_ ∷ []) = refl
    0↔1²-cancel (x ∷ x₁ ∷ xs) = refl

    ⟨0↔1+_⟩²-cancel : ∀ {n} (i : Fin n) → ⟨0↔1+ i ⟩ ² ≗ id {A = Vec A (1 + n)}
    ⟨0↔1+ zero  ⟩²-cancel xs = 0↔1²-cancel xs
    ⟨0↔1+ suc i ⟩²-cancel xs
      rewrite 0↔1²-cancel (map-tail ⟨0↔1+ i ⟩ (0↔1 xs))
            | map-tail∘map-tail ⟨0↔1+ i ⟩ ⟨0↔1+ i ⟩ (0↔1 xs)
            | map-tail-≗ _ _ ⟨0↔1+ i ⟩²-cancel (0↔1 xs)
            | map-tail-id (0↔1 xs)
            | 0↔1²-cancel xs = refl

    ⟨0↔_⟩²-cancel : ∀ {n} (i : Fin n) → ⟨0↔ i ⟩ ² ≗ id {A = Vec A n}
    ⟨0↔ zero  ⟩²-cancel _  = ≡.refl
    ⟨0↔ suc i ⟩²-cancel xs = ⟨0↔1+ i ⟩²-cancel xs

    ⟨_↔_⟩²-cancel : ∀ {n} (i j : Fin n) → ⟨ i ↔ j ⟩ ² ≗ id
    ⟨ zero  ↔ j     ⟩²-cancel xs = ⟨0↔ j   ⟩²-cancel xs
    ⟨ suc i ↔ zero  ⟩²-cancel xs = ⟨0↔1+ i ⟩²-cancel xs
    ⟨ suc i ↔ suc j ⟩²-cancel xs
      rewrite map-tail∘map-tail ⟨ i ↔ j ⟩ ⟨ i ↔ j ⟩ xs
            | map-tail-≗ _ _ ⟨ i ↔ j ⟩²-cancel xs
            | map-tail-id xs = refl

    lem01maptail2 : ∀ {m n a} {A : Set a} (f : Vec A m → Vec A n) →
                      0↔1 ∘ map-tail (map-tail f) ∘ 0↔1 ≗ map-tail (map-tail f)
    lem01maptail2 _ (_ ∷ _ ∷ _) = refl

    ↔-refl : ∀ {n} (i : Fin n) → ⟨ i ↔ i ⟩ ≗ id
    ↔-refl zero    _  = refl
    ↔-refl (suc i) xs rewrite map-tail-≗ _ _ (↔-refl i) xs = map-tail-id xs

    {-
    lem1+ : ∀ {n} (i j : Fin n) → ⟨0↔1+ i ⟩ ∘ ⟨0↔1+ j ⟩ ∘ ⟨0↔1+ i ⟩ ≗ map-tail ⟨ i ↔ j ⟩
    lem1+ zero zero xs = {!!}
    lem1+ zero (suc j) xs = {!!}
    lem1+ (suc i) zero xs = {!!}
    lem1+ (suc i) (suc j) xs
      rewrite 0↔1²-cancel (map-tail ⟨0↔1+ i ⟩ (0↔1 xs))
            | 0↔1²-cancel (map-tail ⟨0↔1+ j ⟩ (map-tail ⟨0↔1+ i ⟩ (0↔1 xs)))
            | map-tail∘map-tail ⟨0↔1+ j ⟩ ⟨0↔1+ i ⟩ (0↔1 xs)
            | map-tail∘map-tail ⟨0↔1+ i ⟩ (⟨0↔1+ j ⟩ ∘ ⟨0↔1+ i ⟩) (0↔1 xs)
            | map-tail-≗ _ _ (lem1+ i j) (0↔1 xs)
            | lem01maptail2 ⟨ i ↔ j ⟩ xs
            = refl

    lem : ∀ {n} (i j : Fin n) → ⟨0↔ i ⟩ ∘ ⟨0↔ j ⟩ ∘ ⟨0↔ i ⟩ ≗ ⟨ i ↔ j ⟩
    lem zero j xs = refl
    lem (suc i) zero xs = {!⟨0↔1+ i ⟩²-cancel xs!}
    lem (suc i) (suc j) xs = (⟨0↔1+ i ⟩ ∘ ⟨0↔1+ j ⟩ ∘ ⟨0↔1+ i ⟩) xs
                 ≡⟨ lem1+ i j xs ⟩
                   ⟨ suc i ↔ suc j ⟩ xs
                 ∎ where open ≡-Reasoning
    test = {!!}
    -}
{-
    lem : ∀ {n} (i j k : Fin n) → ⟨ i ↔ j ⟩ ∘ ⟨ i ↔ k ⟩ ∘ ⟨ i ↔ j ⟩ ≗ ⟨ j ↔ k ⟩
    lem i j k xs = (⟨ i ↔ j ⟩ ∘ ⟨ i ↔ k ⟩ ∘ ⟨ i ↔ j ⟩) xs
                   (⟨ i ↔ j ⟩ ∘ ⟨ i ↔ k ⟩ ∘ id ∘ ⟨ i ↔ j ⟩) xs
                   (⟨ i ↔ j ⟩ ∘ ⟨ i ↔ k ⟩ ∘ ⟨ i ↔ k ⟩ ∘ ⟨ i ↔ k ⟩ ∘ ⟨ i ↔ j ⟩) xs
                 ≡⟨ {!!} ⟩
                   ⟨ j ↔ k ⟩ xs
                 ∎ where open ≡-Reasoning
-}
⟨_↔_⟩ : ∀ {n} (i j : Fin n) {a} {A : Set a} → Vec A n → Vec A n
⟨_↔_⟩ i j = ⟨↔⟩.⟨_↔_⟩ _ i j

module PermutationSyntax where
    infixr 1 _`⁏_
    data Perm : Set where
      `id `0↔1 : Perm
      _`⁏_ : Perm → Perm → Perm
      `tl : Perm → Perm

    _⁻¹ : Endo Perm
    `id ⁻¹ = `id
    (f₀ `⁏ f₁) ⁻¹ = f₁ ⁻¹ `⁏ f₀ ⁻¹
    `0↔1 ⁻¹ = `0↔1
    (`tl f) ⁻¹ = `tl (f ⁻¹)

    `⟨0↔1+_⟩ : ∀ {n} (i : Fin n) → Perm
    `⟨0↔1+ zero  ⟩ = `0↔1
    `⟨0↔1+ suc i ⟩ = `0↔1 `⁏ `tl `⟨0↔1+ i ⟩ `⁏ `0↔1

    `⟨0↔_⟩ : ∀ {n} (i : Fin n) → Perm
    `⟨0↔ zero  ⟩ = `id
    `⟨0↔ suc i ⟩ = `⟨0↔1+ i ⟩

    `⟨_↔_⟩ : ∀ {n} (i j : Fin n) → Perm
    `⟨ zero  ↔ j     ⟩ = `⟨0↔ j ⟩
    `⟨ i     ↔ zero  ⟩ = `⟨0↔ i ⟩
    `⟨ suc i ↔ suc j ⟩ = `tl `⟨ i ↔ j ⟩

module PermutationSemantics {a} {A : Set a} where
    open PermutationSyntax

    eval : Perm → ∀ {n} → Endo (Vec A n)
    eval `id             = id
    eval (f `⁏ g)        = eval g ∘ eval f
    eval `0↔1            = 0↔1
    eval (`tl f) {zero}  = id
    eval (`tl f) {suc n} = λ xs → head xs ∷ eval f (tail xs)

    infixr 9 _∙_
    _∙_ : Perm → ∀ {n} → Endo (Vec A n)
    _∙_ = eval

    `⟨0↔1+_⟩-spec : ∀ {n} (i : Fin n) (xs : Vec A (suc n)) → `⟨0↔1+ i ⟩ ∙ xs ≡ ⟨0↔1+ i ⟩ xs
    `⟨0↔1+ zero  ⟩-spec xs = refl
    `⟨0↔1+ suc i ⟩-spec (x ∷ y ∷ xs) rewrite `⟨0↔1+ i ⟩-spec (x ∷ xs) = refl

    `⟨0↔_⟩-spec : ∀ {n} (i : Fin n) (xs : Vec A n) → `⟨0↔ i ⟩ ∙ xs ≡ ⟨0↔ i ⟩ xs
    `⟨0↔ zero  ⟩-spec xs = refl
    `⟨0↔ suc i ⟩-spec xs = `⟨0↔1+ i ⟩-spec xs

    _≗′_ : Perm → Perm → Set _
    f ≗′ g = ∀ {n} (xs : Vec A n) → f ∙ xs ≡ g ∙ xs

    open ⟨↔⟩ A hiding (⟨_↔_⟩)

    _⁻¹-inverse : ∀ f → (f `⁏ f ⁻¹) ≗′ `id
    (`id ⁻¹-inverse) xs = refl
    ((f `⁏ g) ⁻¹-inverse) xs
      rewrite (g ⁻¹-inverse) (f ∙ xs)
            | (f ⁻¹-inverse) xs = refl
    (`0↔1 ⁻¹-inverse) xs = 0↔1²-cancel xs
    ((`tl f) ⁻¹-inverse) [] = refl
    ((`tl f) ⁻¹-inverse) (x ∷ xs)
      rewrite (f ⁻¹-inverse) xs = refl

    _⁻¹-involutive : ∀ f → (f ⁻¹) ⁻¹ ≗′ f
    (`id ⁻¹-involutive) _ = refl
    ((f `⁏ g) ⁻¹-involutive) x
      rewrite (f ⁻¹-involutive) x
            | (g ⁻¹-involutive) (f ∙ x) = refl
    (`0↔1 ⁻¹-involutive) _ = refl
    ((`tl f) ⁻¹-involutive) [] = refl
    ((`tl f) ⁻¹-involutive) (x ∷ xs)
      rewrite (f ⁻¹-involutive) xs
            = refl

    _⁻¹-inverse′ : ∀ f → (f ⁻¹ `⁏ f) ≗′ `id
    (f ⁻¹-inverse′) xs with ((f ⁻¹) ⁻¹-inverse) xs
    ... | p rewrite (f ⁻¹-involutive) (f ⁻¹ ∙ xs) = p

    `⟨_↔_⟩-spec : ∀ {n} (i j : Fin n) (xs : Vec A n) → `⟨ i ↔ j ⟩ ∙ xs ≡ ⟨ i ↔ j ⟩ xs
    `⟨_↔_⟩-spec zero    j       xs = `⟨0↔   j ⟩-spec xs
    `⟨_↔_⟩-spec (suc i) zero    xs = `⟨0↔1+ i ⟩-spec xs
    `⟨_↔_⟩-spec (suc i) (suc j) (x ∷ xs)
       rewrite `⟨ i ↔ j ⟩-spec xs = refl

module PermutationProperties {a : L.Level} where
    open PermutationSyntax
    open PermutationSemantics

    ⊛-dist-∙ : ∀ {n} {A : Set a} (fs : Vec (Endo A) n) (f : Perm) xs → (f ∙ fs ⊛ f ∙ xs) ≡ f ∙ (fs ⊛ xs)
    ⊛-dist-∙ _       `id        _  = refl
    ⊛-dist-∙ fs      `0↔1       xs = ⊛-dist-0↔1 fs xs
    ⊛-dist-∙ []       (`tl _)   [] = refl
    ⊛-dist-∙ (_ ∷ fs) (`tl f)   (_ ∷ xs) rewrite ⊛-dist-∙ fs f xs = refl
    ⊛-dist-∙ fs       (f `⁏ g)   xs rewrite ⊛-dist-∙ (f ∙ fs) g (f ∙ xs)
                                         | ⊛-dist-∙ fs f xs = refl

    ∙-replicate : ∀ n {A : Set a} (x : A) f → f ∙ replicate {n = n} x ≡ replicate x
    ∙-replicate n x `id = refl
    ∙-replicate zero x `0↔1 = refl
    ∙-replicate (suc zero) x `0↔1 = refl
    ∙-replicate (suc (suc n)) x `0↔1 = refl
    ∙-replicate zero x (`tl _) = refl
    ∙-replicate (suc n) x (`tl f) rewrite ∙-replicate n x f = refl
    ∙-replicate n x (f `⁏ g) rewrite ∙-replicate n x f | ∙-replicate n x g = refl

    private
        lem : ∀ {n} {A : Set a} (fs : Vec (Endo A) n) f xs → fs ⊛ f ∙ xs ≡ f ∙ (f ⁻¹ ∙ fs ⊛ xs)
        lem fs f xs rewrite sym (⊛-dist-∙ (f ⁻¹ ∙ fs) f xs) | (f ⁻¹-inverse′) fs = refl

    ∙-map : ∀ {n} {A : Set a} (f : Endo A) g (xs : Vec A n) → map f (g ∙ xs) ≡ g ∙ map f xs
    ∙-map {n} f g xs rewrite sym (⊛-dist-∙ (replicate f) g xs) | ∙-replicate n f g = refl

module BijectionSyntax {a b} (A : Set a) (Bijᴬ : Set b) where
    infixr 1 _`⁏_
    data Bij : Set (a L.⊔ b) where
      `id `0↔1 : Bij
      _`⁏_ : Bij → Bij → Bij
      _`∷_ : Bijᴬ → (A → Bij) → Bij

module BijectionLib where
    open BijectionSyntax
    mapBij : ∀ {a bᴬ} {A : Set a} {Bijᴬ : Set bᴬ}
               {b bᴮ} {B : Set b} {Bijᴮ : Set bᴮ}
             → (B → A)
             → (Bijᴬ → Bijᴮ)
             → Bij A Bijᴬ → Bij B Bijᴮ
    mapBij fᴮᴬ f `id = `id
    mapBij fᴮᴬ f `0↔1 = `0↔1
    mapBij fᴮᴬ f (`g `⁏ `h) = mapBij fᴮᴬ f `g `⁏ mapBij fᴮᴬ f `h
    mapBij fᴮᴬ f (`fᴬ `∷ `g) = f `fᴬ `∷ λ x → mapBij fᴮᴬ f (`g (fᴮᴬ x))

module BijectionSemantics {a b} {A : Set a} (bijKitᴬ : BijKit b A) where
    open BijKit bijKitᴬ renaming (Bij to Bijᴬ; eval to evalᴬ; _⁻¹ to _⁻¹ᴬ;
                                  idBij to idᴬ; _≗Bij_ to _≗ᴬ_;
                                  _⁻¹-inverse to _⁻¹-inverseᴬ;
                                  _⁻¹-involutive to _⁻¹-involutiveᴬ;
                                  id-spec to idᴬ-spec)
    open BijectionSyntax A Bijᴬ

    _⁻¹ : Endo Bij
    `id ⁻¹ = `id
    (f₀ `⁏ f₁) ⁻¹ = f₁ ⁻¹ `⁏ f₀ ⁻¹
    `0↔1 ⁻¹ = `0↔1
    (fᴬ `∷ f) ⁻¹ = fᴬ⁻¹ `∷ λ x → (f (evalᴬ fᴬ⁻¹ x))⁻¹ where fᴬ⁻¹ = fᴬ ⁻¹ᴬ

    eval : Bij → ∀ {n} → Endo (Vec A n)
    eval `id               = id
    eval (f `⁏ g)          = eval g ∘ eval f
    eval `0↔1              = 0↔1
    eval (fᴬ `∷ f) {zero}  = id
    eval (fᴬ `∷ f) {suc n} = λ xs → evalᴬ fᴬ (head xs) ∷ eval (f (head xs)) (tail xs)

    infixr 9 _∙_
    _∙_ : Bij → ∀ {n} → Endo (Vec A n)
    _∙_ = eval

    _≗′_ : Bij → Bij → Set _
    f ≗′ g = ∀ {n} (xs : Vec A n) → f ∙ xs ≡ g ∙ xs

    _⁻¹-inverse : ∀ f → (f `⁏ f ⁻¹) ≗′ `id
    (`id ⁻¹-inverse) xs = refl
    ((f `⁏ g) ⁻¹-inverse) xs
      rewrite (g ⁻¹-inverse) (f ∙ xs)
            | (f ⁻¹-inverse) xs = refl
    (`0↔1 ⁻¹-inverse) xs = ⟨↔⟩.0↔1²-cancel _ xs
    ((fᴬ `∷ f) ⁻¹-inverse) [] = refl
    ((fᴬ `∷ f) ⁻¹-inverse) (x ∷ xs)
      rewrite (fᴬ ⁻¹-inverseᴬ) x | (f x ⁻¹-inverse) xs = refl

    _⁻¹-involutive : ∀ f → (f ⁻¹) ⁻¹ ≗′ f
    (`id ⁻¹-involutive) _ = refl
    ((f `⁏ g) ⁻¹-involutive) x
      rewrite (f ⁻¹-involutive) x
            | (g ⁻¹-involutive) (f ∙ x) = refl
    (`0↔1 ⁻¹-involutive) _ = refl
    ((fᴬ `∷ f) ⁻¹-involutive) [] = refl
    ((fᴬ `∷ f) ⁻¹-involutive) (x ∷ xs)
      rewrite (fᴬ ⁻¹-involutiveᴬ) x
            | (fᴬ ⁻¹-inverseᴬ) x
            | (f x ⁻¹-involutive) xs
            = refl

    Vec-bijKit : ∀ n → BijKit _ (Vec A n)
    Vec-bijKit n = mk Bij (λ f → eval f {n}) _⁻¹ `id _`⁏_ (λ _ → refl) (λ _ _ _ → refl)
                (λ f x → _⁻¹-inverse f x) (λ f x → _⁻¹-involutive f x)

    module VecBijKit n = BijKit (Vec-bijKit n)

    `tl : Endo Bij
    `tl f = idᴬ `∷ const f

    private
      module P where
        open PermutationSyntax public
        open PermutationSemantics {A = A} public
    open P using (Perm; `id; `0↔1; _`⁏_)
    fromPerm : Perm → Bij
    fromPerm `id = `id
    fromPerm `0↔1 = `0↔1
    fromPerm (π₀ `⁏ π₁) = fromPerm π₀ `⁏ fromPerm π₁
    fromPerm (P.`tl π) = `tl (fromPerm π)

    fromPerm-spec : ∀ π {n} (xs : Vec A n) → π P.∙ xs ≡ fromPerm π ∙ xs
    fromPerm-spec `id xs = refl
    fromPerm-spec `0↔1 xs = refl
    fromPerm-spec (π `⁏ π₁) xs rewrite fromPerm-spec π xs | fromPerm-spec π₁ (fromPerm π ∙ xs) = refl
    fromPerm-spec (P.`tl π) [] = refl
    fromPerm-spec (P.`tl π) (x ∷ xs) rewrite idᴬ-spec x | fromPerm-spec π xs = refl

    private
      module Unused where
        `⟨0↔1+_⟩ : ∀ {n} (i : Fin n) → Bij
        `⟨0↔1+ i ⟩ = fromPerm P.`⟨0↔1+ i ⟩

        `⟨0↔1+_⟩-spec : ∀ {n} (i : Fin n) (xs : Vec A (suc n)) → `⟨0↔1+ i ⟩ ∙ xs ≡ ⟨0↔1+ i ⟩ xs
        `⟨0↔1+ i ⟩-spec xs rewrite sym (P.`⟨0↔1+ i ⟩-spec xs) | fromPerm-spec P.`⟨0↔1+ i ⟩ xs = refl

        `⟨0↔_⟩ : ∀ {n} (i : Fin n) → Bij
        `⟨0↔ i ⟩ = fromPerm P.`⟨0↔ i ⟩

        `⟨0↔_⟩-spec : ∀ {n} (i : Fin n) (xs : Vec A n) → `⟨0↔ i ⟩ ∙ xs ≡ ⟨0↔ i ⟩ xs
        `⟨0↔ i ⟩-spec xs rewrite sym (P.`⟨0↔ i ⟩-spec xs) | fromPerm-spec P.`⟨0↔ i ⟩ xs = refl

    `⟨_↔_⟩ : ∀ {n} (i j : Fin n) → Bij
    `⟨ i ↔ j ⟩ = fromPerm P.`⟨ i ↔ j ⟩

    `⟨_↔_⟩-spec : ∀ {n} (i j : Fin n) (xs : Vec A n) → `⟨ i ↔ j ⟩ ∙ xs ≡ ⟨ i ↔ j ⟩ xs
    `⟨ i ↔ j ⟩-spec xs rewrite sym (P.`⟨ i ↔ j ⟩-spec xs) | fromPerm-spec P.`⟨ i ↔ j ⟩ xs = refl

private
  module Unused where
    module Foo where
    {-
       WRONG
        ⟨_↔_⟩ : ∀ {n} (i j : Fin n) {a} {A : Set a} → Vec A n → Vec A n
        ⟨ i ↔ j ⟩ = ⟨0↔ i ⟩ ∘ ⟨0↔ j ⟩ ∘ ⟨0↔ i ⟩

        ⟨0↔⟩-spec : ∀ {n a} {A : Set a} (i : Fin (suc n)) → ⟨0↔ i ⟩ ≗ ⟨ zero ↔ i ⟩ {A = A}
        ⟨0↔⟩-spec _ _ = ≡.refl
        -}

    ⟨0↔_⟩′ : ∀ {n} (i : Fin n) {a} {A : Set a} → Vec A n → Vec A n
    ⟨0↔_⟩′ {zero}  i xs = xs
    ⟨0↔_⟩′ {suc n} i xs = lookup i xs ∷ tail (xs [ i ]≔ head xs)

    -- ⟨ i ↔+1⟩: Exchange elements at position i and i + 1.
    ⟨_↔+1⟩ : ∀ {n} (i : Fin n) {a} {A : Set a} → Vec A n → Vec A n
    ⟨ zero  ↔+1⟩ = 0↔1
    ⟨ suc i ↔+1⟩ = map-tail ⟨ i ↔+1⟩

    ⟨↔+1⟩-spec : ∀ {n} (i : Fin n) {a} {A : Set a} → ⟨ inject₁ i ↔+1⟩ ≗ ⟨ inject₁ i ↔ suc i ⟩ {A = A}
    ⟨↔+1⟩-spec zero    xs       rewrite map-tail-id (0↔1 xs) = ≡.refl
    ⟨↔+1⟩-spec (suc i) (x ∷ xs) rewrite ⟨↔+1⟩-spec i xs = ≡.refl

    -- rot-up-to i (x₀ ∷ x₁ ∷ x₂ ∷ … ∷ xᵢ ∷ xs)
    --           ≡ (x₁ ∷ x₂ ∷ x₃ ∷ … ∷ x₀ ∷ xs)
    rot-up-to : ∀ {n} (i : Fin n) {a} {A : Set a} → Vec A n → Vec A n
    rot-up-to zero    = id
    rot-up-to (suc i) = map-tail (rot-up-to i) ∘ 0↔1

    -- Inverse of rot-up-to
    rot⁻¹-up-to : ∀ {n} (i : Fin n) {a} {A : Set a} → Vec A n → Vec A n
    rot⁻¹-up-to zero    = id
    rot⁻¹-up-to (suc i) = 0↔1 ∘ map-tail (rot⁻¹-up-to i)

    rot⁻¹-up-to∘rot-up-to : ∀ {n} (i : Fin n) {a} {A : Set a} → rot⁻¹-up-to i ∘ rot-up-to i ≗ id {a} {Vec A n}
    rot⁻¹-up-to∘rot-up-to zero            _ = ≡.refl
    rot⁻¹-up-to∘rot-up-to (suc i) {A = A} (x₀ ∷ []) rewrite rot⁻¹-up-to∘rot-up-to i {A = A} [] = ≡.refl
    rot⁻¹-up-to∘rot-up-to (suc i)         (x₀ ∷ x₁ ∷ xs) rewrite rot⁻¹-up-to∘rot-up-to i (x₀ ∷ xs) = ≡.refl
