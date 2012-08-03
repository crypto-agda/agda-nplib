module Data.Vec.NP where

open import Data.Vec public hiding (_⊛_; zipWith; zip; map)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin renaming (_+_ to _+ᶠ_)
open import Data.Fin.Props
open import Data.Bool
open import Data.Product hiding (map; zip)
open import Function
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡

module waiting-for-a-fix-in-the-stdlib where

    infixl 4 _⊛_

    _⊛_ : ∀ {a b n} {A : Set a} {B : Set b} →
          Vec (A → B) n → Vec A n → Vec B n
    _⊛_ {n = zero}  fs xs = []
    _⊛_ {n = suc n} fs xs = head fs (head xs) ∷ (tail fs ⊛ tail xs)

    map : ∀ {a b n} {A : Set a} {B : Set b} →
          (A → B) → Vec A n → Vec B n
    map f xs = replicate f ⊛ xs

    zipWith : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c} →
              (A → B → C) → Vec A n → Vec B n → Vec C n
    zipWith _⊕_ xs ys = replicate _⊕_ ⊛ xs ⊛ ys

    zip : ∀ {a b n} {A : Set a} {B : Set b} →
          Vec A n → Vec B n → Vec (A × B) n
    zip = zipWith _,_

open waiting-for-a-fix-in-the-stdlib public

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
... | false rewrite inject₁-lemma (countᶠ pred (map f xs))
                  | inject₁-lemma (countᶠ (pred ∘ f) xs)
                  | count-∘ f pred xs = refl

count-++ : ∀ {m n a} {A : Set a} (pred : A → Bool) (xs : Vec A m) (ys : Vec A n)
            → count pred (xs ++ ys) ≡ count pred xs + count pred ys
count-++ pred [] ys = refl
count-++ pred (x ∷ xs) ys with pred x
... | true  rewrite count-++ pred xs ys = refl
... | false rewrite inject₁-lemma (countᶠ pred (xs ++ ys))
                  | inject₁-lemma (countᶠ pred xs) | count-++ pred xs ys = refl

ext-countᶠ : ∀ {n a} {A : Set a} {f g : A → Bool} → f ≗ g → (xs : Vec A n) → countᶠ f xs ≡ countᶠ g xs
ext-countᶠ f≗g [] = refl
ext-countᶠ f≗g (x ∷ xs) rewrite ext-countᶠ f≗g xs | f≗g x = refl

filter : ∀ {n a} {A : Set a} (pred : A → Bool) (xs : Vec A n) → Vec A (count pred xs)
filter pred [] = []
filter pred (x ∷ xs) with pred x
... | true  = x ∷ filter pred xs
... | false rewrite inject₁-lemma (countᶠ pred xs) = filter pred xs

η : ∀ {n a} {A : Set a} → Vec A n → Vec A n
η = tabulate ∘ flip lookup

η′ : ∀ {n a} {A : Set a} → Vec A n → Vec A n
η′ {zero}  = λ _ → []
η′ {suc n} = λ xs → head xs ∷ η (tail xs)

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

map-tail : ∀ {m n a} {A : Set a} → (Vec A m → Vec A n) → Vec A (suc m) → Vec A (suc n)
map-tail f (x ∷ xs) = x ∷ f xs

map-tail-id : ∀ {n a} {A : Set a} → map-tail id ≗ id {A = Vec A (suc n)}
map-tail-id (x ∷ xs) = ≡.refl

-- ⟨ i ↔+1⟩: Exchange elements at position i and i + 1.
⟨_↔+1⟩ : ∀ {n} (i : Fin n) {a} {A : Set a} → Vec A n → Vec A n
⟨ zero  ↔+1⟩ = 0↔1
⟨ suc i ↔+1⟩ = map-tail ⟨ i ↔+1⟩

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

-- ⟨0↔ i ⟩: Exchange elements at position 0 and i.
⟨0↔_⟩ : ∀ {n} (i : Fin n) {a} {A : Set a} → Vec A n → Vec A n
⟨0↔ zero  ⟩ = id
⟨0↔ suc i ⟩ = rot⁻¹-up-to (inject₁ i) ∘ rot-up-to (suc i)

⟨0↔zero⟩ : ∀ {n a} {A : Set a} → ⟨0↔ zero ⟩ ≗ id {A = Vec A (suc n)}
⟨0↔zero⟩ _ = ≡.refl

-- ⟨ i ↔ j ⟩: Exchange elements at position i and j.
⟨_↔_⟩ : ∀ {n} (i j : Fin n) {a} {A : Set a} → Vec A n → Vec A n
⟨ i ↔ j ⟩ = ⟨0↔ i ⟩ ∘ ⟨0↔ j ⟩ ∘ ⟨0↔ i ⟩

⟨0↔⟩-spec : ∀ {n a} {A : Set a} (i : Fin (suc n)) → ⟨0↔ i ⟩ ≗ ⟨ zero ↔ i ⟩ {A = A}
⟨0↔⟩-spec _ _ = ≡.refl

⟨_↔_⟩′ : ∀ {n} (i j : Fin n) {a} {A : Set a} → Vec A n → Vec A n
⟨ zero  ↔ j     ⟩′ = ⟨0↔ j ⟩
⟨ i     ↔ zero  ⟩′ = ⟨0↔ i ⟩
⟨ suc i ↔ suc j ⟩′ = map-tail ⟨ i ↔ j ⟩′

⟨↔⟩′-comm : ∀ {n a} {A : Set a} (i j : Fin n) → ⟨ i ↔ j ⟩′ ≗ ⟨ j ↔ i ⟩′ {A = A}
⟨↔⟩′-comm zero    zero    _ = ≡.refl
⟨↔⟩′-comm zero    (suc _) _ = ≡.refl
⟨↔⟩′-comm (suc _) zero    _ = ≡.refl
⟨↔⟩′-comm (suc i) (suc j) (x ∷ xs) rewrite ⟨↔⟩′-comm i j xs = ≡.refl

⟨↔+1⟩-spec : ∀ {n} (i : Fin n) {a} {A : Set a} → ⟨ inject₁ i ↔+1⟩ ≗ ⟨ inject₁ i ↔ suc i ⟩′ {A = A}
⟨↔+1⟩-spec zero    xs       rewrite map-tail-id (0↔1 xs) = ≡.refl
⟨↔+1⟩-spec (suc i) (x ∷ xs) rewrite ⟨↔+1⟩-spec i xs = ≡.refl

⟨0↔_⟩′ : ∀ {n} (i : Fin n) {a} {A : Set a} → Vec A n → Vec A n
⟨0↔_⟩′ {zero}  i xs = xs
⟨0↔_⟩′ {suc n} i xs = lookup i xs ∷ tail (xs [ i ]≔ head xs)
