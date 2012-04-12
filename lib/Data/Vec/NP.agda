module Data.Vec.NP where

open import Data.Vec public
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin hiding (_+_)
open import Data.Fin.Props
open import Data.Bool
open import Data.Product
open import Function
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡

count : ∀ {n a} {A : Set a} → (A → Bool) → Vec A n → Fin (suc n)
count pred [] = zero
count pred (x ∷ xs) = (if pred x then suc else inject₁) (count pred xs)

filter : ∀ {n a} {A : Set a} (pred : A → Bool) (xs : Vec A n) → Vec A (toℕ (count pred xs))
filter pred [] = []
filter pred (x ∷ xs) with pred x
... | true  = x ∷ filter pred xs
... | false rewrite inject₁-lemma (count pred xs) = filter pred xs

η : ∀ {n a} {A : Set a} → Vec A n → Vec A n
η = tabulate ∘ flip lookup

η′ : ∀ {n a} {A : Set a} → Vec A n → Vec A n
η′ {zero}  = λ _ → []
η′ {suc n} = λ xs → head xs ∷ η (tail xs)

≡-splitAt : ∀ {m n a} {A : Set a} {xs zs : Vec A m} {ys ts : Vec A n}
             → (xs ++ ys) ≡ (zs ++ ts) → (xs ≡ zs × ys ≡ ts)
≡-splitAt {zero} {xs = []} {[]} p = refl , p
≡-splitAt {suc m} {xs = x ∷ xs} {z ∷ zs} eq with ≡-splitAt {m} {xs = xs} {zs} (cong tail eq)
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
++-inj₁ xs ys eq = proj₁ (≡-splitAt eq)

++-inj₂ : ∀ {m n} {a} {A : Set a} (xs ys : Vec A m) {zs ts : Vec A n} → xs ++ zs ≡ ys ++ ts → zs ≡ ts
++-inj₂ xs ys eq = proj₂ (≡-splitAt {xs = xs} {ys} eq)

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
