{-# OPTIONS --universe-polymorphism #-}
module Function.NP where

open import Type
open import Function       public
open import Data.Nat       using (ℕ; zero; suc; _+_; _*_; fold)
open import Data.Bool      using (Bool)
open import Data.Vec.N-ary using (N-ary; N-ary-level)
import Category.Monad.Identity as Id
open import Category.Monad renaming (module RawMonad to Monad; RawMonad to Monad)
open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Relation.Binary.PropositionalEquality.NP

id-app : ∀ {f} → Applicative {f} id
id-app = rawIApplicative
  where open Monad Id.IdentityMonad

_→⟨_⟩_ : ∀ {a b} (A : Set a) (n : ℕ) (B : Set b) → Set (N-ary-level a b n)
A →⟨ n ⟩ B = N-ary n A B

_→⟨_⟩₀_ : ∀ (A : ★) (n : ℕ) (B : ★) → ★
A →⟨ zero  ⟩₀ B = B
A →⟨ suc n ⟩₀ B = A → A →⟨ n ⟩₀ B

_→⟨_⟩₁_ : ∀ (A : ★) (n : ℕ) (B : ★₁) → ★₁
A →⟨ zero  ⟩₁ B = B
A →⟨ suc n ⟩₁ B = A → A →⟨ n ⟩₁ B

Endo : ∀ {a} → Set a → Set a
Endo A = A → A

Cmp : ∀ {a} → Set a → Set a
Cmp A = A → A → Bool

-- More properties about fold are in Data.Nat.NP
nest : ∀ {a} {A : Set a} → ℕ → Endo (Endo A)
-- TMP nest n f x = fold x f n
nest zero f x = x
nest (suc n) f x = f (nest n f x)

module nest-Properties {a} {A : Set a} (f : Endo A) where
  nest₀ : nest 0 f ≡ id
  nest₀ = refl
  nest₁ : nest 1 f ≡ f
  nest₁ = refl
  nest₂ : nest 2 f ≡ f ∘ f
  nest₂ = refl
  nest₃ : nest 3 f ≡ f ∘ f ∘ f
  nest₃ = refl

  nest-+ : ∀ m n → nest (m + n) f ≡ nest m f ∘ nest n f
  nest-+ zero    n = refl
  nest-+ (suc m) n = cong (_∘_ f) (nest-+ m n)

  nest-+' : ∀ m n → nest (m + n) f ≗ nest m f ∘ nest n f
  nest-+' m n x = cong (flip _$_ x) (nest-+ m n)

  nest-* : ∀ m n → nest (m * n) f ≗ nest m (nest n f)
  nest-* zero n x = refl
  nest-* (suc m) n x =
    nest (suc m * n) f x             ≡⟨ refl ⟩
    nest (n + m * n) f x             ≡⟨ nest-+' n (m * n) x ⟩
    (nest n f ∘ nest (m * n) f) x    ≡⟨ cong (nest n f) (nest-* m n x) ⟩
    (nest n f ∘ nest m (nest n f)) x ≡⟨ refl ⟩
    nest n f (nest m (nest n f) x)   ≡⟨ refl ⟩
    nest (suc m) (nest n f) x ∎
   where open ≡-Reasoning

{- WRONG
module more-nest-Properties {a} {A : Set a} where
  nest-+'' : ∀ (f : Endo (Endo A)) g m n → nest m f g ∘ nest n f g ≗ nest (m + n) f g
  nest-+'' f g zero n = {!!}
  nest-+'' f g (suc m) n = {!!} 
-}

_$⟨_⟩_ : ∀ {a} {A : Set a} → Endo A → ℕ → Endo A
_$⟨_⟩_ f n = nest n f

-- If you run a version of Agda without the support of instance
-- arguments, simply comment this definition, very little code rely on it.
… : ∀ {a} {A : Set a} ⦃ x : A ⦄ → A
… ⦃ x ⦄ = x

module Combinators where
    S : ∀ {A B C : ★} →
          (A → B → C) →
          (A → B) →
          (A → C)
    S = _ˢ_

    K : ∀ {A B : ★} → A → B → A
    K = const

    -- B ≗ _∘_
    B : ∀ {A B C : ★} → (B → C) → (A → B) → A → C
    B = S (K S) K

    -- C ≗ flip
    C : ∀ {A B C : ★} → (A → B → C) → B → A → C
    C = S (S (K (S (K S) K)) S) (K K)
