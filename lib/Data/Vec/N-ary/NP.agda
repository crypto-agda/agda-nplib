module Data.Vec.N-ary.NP where

open import Function
open import Data.Nat
open import Data.Vec
open import Data.Vec.N-ary public renaming (curryⁿ to curryⁿ′; _$ⁿ_ to _$ⁿ′_)
open import Relation.Binary.PropositionalEquality

curryⁿ : ∀ {n a b} {A : Set a} {B : N-ary n A (Set b)} →
         ((xs : Vec A n) → B $ⁿ′ xs) → ∀ⁿ n B
curryⁿ {zero}  f = f []
curryⁿ {suc n} f = λ x → curryⁿ (f ∘ _∷_ x)

_$ⁿ_ : ∀ {n a b} {A : Set a} {B : N-ary n A (Set b)} → ∀ⁿ n B → ((xs : Vec A n) → B $ⁿ′ xs)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

curry-$ⁿ : ∀ {n a b} {A : Set a} {B : N-ary n A (Set b)} (f : (xs : Vec A n) → B $ⁿ′ xs) (xs : Vec A n)
           → curryⁿ f $ⁿ xs ≡ f xs
curry-$ⁿ f []       = refl
curry-$ⁿ f (x ∷ xs) = curry-$ⁿ (f ∘ _∷_ x) xs

curry-$ⁿ′ : ∀ {n a b} {A : Set a} {B : Set b} (f : Vec A n → B) (xs : Vec A n)
           → curryⁿ′ f $ⁿ′ xs ≡ f xs
curry-$ⁿ′ f []       = refl
curry-$ⁿ′ f (x ∷ xs) = curry-$ⁿ′ (f ∘ _∷_ x) xs

constⁿ : ∀ n {a b} {A : Set a} {B : Set b} → B → N-ary n A B
constⁿ zero x = x
constⁿ (suc n) x = const (constⁿ n x)

lift₁ : ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) → (∀ x → f x ≡ g x) → ∀ {n} (xs : Vec A n) → map f xs ≡ map g xs
lift₁ f g pf [] = refl
lift₁ f g pf (x ∷ xs) rewrite lift₁ f g pf xs | pf x = refl

-- move it
transpose : ∀ {m n a} {A : Set a} → Vec (Vec A m) n → Vec (Vec A n) m
transpose [] = replicate []
transpose (xs ∷ xss) = zipWith _∷_ xs (transpose xss)

vap' : ∀ {m a b} {A : Set a} {B : Set b} (f : Vec A m → B)
       → ∀ {n} → Vec (Vec A m) n → Vec B n
vap' f [] = []
vap' f (xs ∷ xs₁) = f xs ∷ vap' f xs₁

vap'' : ∀ {m a b} {A : Set a} {B : Set b} (f : Vec A m → B)
        → ∀ {n} → Vec (Vec A n) m → Vec B n
vap'' f = vap' f ∘ transpose

vap : ∀ {m a b} {A : Set a} {B : Set b} (f : N-ary m A B)
       → ∀ {n} → N-ary m (Vec A n) (Vec B n)
vap {m} f = curryⁿ′ {m} (λ xs → vap'' (_$ⁿ′_ f) xs)

lift' : ∀ {m a b} {A : Set a} {B : Set b} (f g : Vec A m → B)
       → (∀ (xs : Vec A m) → f xs ≡ g xs)
       → ∀ {n : ℕ} (xs : Vec (Vec A m) n) → vap' f xs ≡ vap' g xs
lift' f g pf [] = refl
lift' f g pf (x ∷ xs) rewrite lift' f g pf xs | pf x = refl

lift : ∀ {m a b} {A : Set a} {B : Set b} (f g : N-ary m A B)
       → (∀ⁿ m (curryⁿ′ (λ (xs : Vec A m) → f $ⁿ′ xs ≡ g $ⁿ′ xs)))
       → ∀ {n} → ∀ⁿ m (curryⁿ′ (λ (xs : Vec (Vec A n) m) → vap {m} f $ⁿ′ xs ≡ vap {m} g $ⁿ′ xs))
lift {m} f g pf = curryⁿ helper
  where f' = vap'' {m} (_$ⁿ′_ f)
        g' = vap'' {m} (_$ⁿ′_ g)
        h  = λ (xs : Vec _ m) → curryⁿ′ f' $ⁿ′ xs ≡ curryⁿ′ g' $ⁿ′ xs
        hh = λ (xs : Vec _ m) → f $ⁿ′ xs ≡ g $ⁿ′ xs
        pf' : ∀ xs → hh xs
        pf' xs rewrite sym (curry-$ⁿ′ hh xs) = pf $ⁿ xs
        helper : ∀ xs → curryⁿ′ h $ⁿ′ xs
        helper xs rewrite curry-$ⁿ′ h xs | curry-$ⁿ′ f' xs | curry-$ⁿ′ g' xs
          = lift' (_$ⁿ′_ f) (_$ⁿ′_ g) pf' (transpose xs)
