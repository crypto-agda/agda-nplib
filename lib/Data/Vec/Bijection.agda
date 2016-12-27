open import Type hiding (★)
open import Data.Nat hiding (_⊔_)
open import Data.Vec.NP
open import Data.Vec.Permutation
open import Data.Fin using (Fin)
open import Level.NP
open import Function.NP
open import Function.Bijection.SyntaxKit
open import Relation.Binary.PropositionalEquality

module Data.Vec.Bijection where

module BijectionSyntax {a b} (A : ★ a) (Bijᴬ : ★ b) where
    infixr 1 _`⁏_
    data Bij : ℕ → ★ (a ⊔ b) where
      `id : ∀ {n} → Bij n
      `0↔1 : ∀ {n} → Bij (2 + n)
      _`⁏_ : ∀ {n} → Bij n → Bij n → Bij n
      _`∷_ : ∀ {n} → Bijᴬ → (A → Bij n) → Bij (1 + n)

module BijectionLib where
    open BijectionSyntax
    mapBij : ∀ {a bᴬ} {A : ★ a} {Bijᴬ : ★ bᴬ}
               {b bᴮ} {B : ★ b} {Bijᴮ : ★ bᴮ}
               (fᴮᴬ : B → A)
               (f   : Bijᴬ → Bijᴮ)
               {n} → Bij A Bijᴬ n → Bij B Bijᴮ n
    mapBij fᴮᴬ f `id = `id
    mapBij fᴮᴬ f `0↔1 = `0↔1
    mapBij fᴮᴬ f (`g `⁏ `h) = mapBij fᴮᴬ f `g `⁏ mapBij fᴮᴬ f `h
    mapBij fᴮᴬ f (`fᴬ `∷ `g) = f `fᴬ `∷ λ x → mapBij fᴮᴬ f (`g (fᴮᴬ x))

module BijectionSemantics {a b} {A : ★ a} (bijKitᴬ : BijKit b A) where
    open BijKit bijKitᴬ renaming (Bij to Bijᴬ; eval to evalᴬ; _⁻¹ to _⁻¹ᴬ;
                                  idBij to idᴬ; _≗Bij_ to _≗ᴬ_;
                                  _⁻¹-inverse to _⁻¹-inverseᴬ;
                                  _⁻¹-involutive to _⁻¹-involutiveᴬ;
                                  id-spec to idᴬ-spec)
    open BijectionSyntax A Bijᴬ

    infix 10 _⁻¹
    _⁻¹ : ∀ {n} → Endo (Bij n)
    `id ⁻¹ = `id
    (f₀ `⁏ f₁) ⁻¹ = f₁ ⁻¹ `⁏ f₀ ⁻¹
    `0↔1 ⁻¹ = `0↔1
    (fᴬ `∷ f) ⁻¹ = fᴬ⁻¹ `∷ λ x → (f (evalᴬ fᴬ⁻¹ x))⁻¹ where fᴬ⁻¹ = fᴬ ⁻¹ᴬ

    eval : ∀ {n} → Bij n → Endo (Vec A n)
    eval `id       = id
    eval (f `⁏ g)   = eval g ∘ eval f
    eval `0↔1      = 0↔1
    eval (fᴬ `∷ f) = λ xs → evalᴬ fᴬ (head xs) ∷ eval (f (head xs)) (tail xs)

    infixr 9 _·_
    _·_ : ∀ {n} → Bij n → Endo (Vec A n)
    _·_ = eval

    infix 4 _≗′_
    _≗′_ : ∀ {n} → Bij n → Bij n → ★ _
    f ≗′ g = ∀ xs → f · xs ≡ g · xs

    infix 10 _⁻¹-inverse _⁻¹-involutive

    _⁻¹-inverse : ∀ {n} (f : Bij n) → (f `⁏ f ⁻¹) ≗′ `id
    (`id ⁻¹-inverse) xs = refl
    ((f `⁏ g) ⁻¹-inverse) xs
      rewrite (g ⁻¹-inverse) (f · xs)
            | (f ⁻¹-inverse) xs = refl
    (`0↔1 ⁻¹-inverse) xs = ⟨↔⟩.0↔1²-cancel _ xs
    ((fᴬ `∷ f) ⁻¹-inverse) (x ∷ xs)
      rewrite (fᴬ ⁻¹-inverseᴬ) x | (f x ⁻¹-inverse) xs = refl

    _⁻¹-involutive : ∀ {n} (f : Bij n) → (f ⁻¹) ⁻¹ ≗′ f
    (`id ⁻¹-involutive) _ = refl
    ((f `⁏ g) ⁻¹-involutive) x
      rewrite (f ⁻¹-involutive) x
            | (g ⁻¹-involutive) (f · x) = refl
    (`0↔1 ⁻¹-involutive) _ = refl
    ((fᴬ `∷ f) ⁻¹-involutive) (x ∷ xs)
      rewrite (fᴬ ⁻¹-involutiveᴬ) x
            | (fᴬ ⁻¹-inverseᴬ) x
            | (f x ⁻¹-involutive) xs
            = refl

    Vec-bijKit : ∀ n → BijKit _ (Vec A n)
    Vec-bijKit n = mk (Bij n) eval _⁻¹ `id _`⁏_ (λ _ → refl) (λ _ _ _ → refl)
                (λ f x → _⁻¹-inverse f x) (λ f x → _⁻¹-involutive f x)

    module VecBijKit n = BijKit (Vec-bijKit n)

    `tl : ∀ {n} → Bij n → Bij (1 + n)
    `tl f = idᴬ `∷ const f

    private
      module P where
        open PermutationSyntax public
        open PermutationSemantics {A = A} public
    open P using (Perm; `id; `0↔1; _`⁏_)
    fromPerm : ∀ {n} → Perm n → Bij n
    fromPerm `id = `id
    fromPerm `0↔1 = `0↔1
    fromPerm (π₀ `⁏ π₁) = fromPerm π₀ `⁏ fromPerm π₁
    fromPerm (P.`tl π) = `tl (fromPerm π)

    fromPerm-spec : ∀ {n} π (xs : Vec A n) → π P.· xs ≡ fromPerm π · xs
    fromPerm-spec `id xs = refl
    fromPerm-spec `0↔1 xs = refl
    fromPerm-spec (π `⁏ π₁) xs rewrite fromPerm-spec π xs | fromPerm-spec π₁ (fromPerm π · xs) = refl
    fromPerm-spec (P.`tl π) (x ∷ xs) rewrite idᴬ-spec x | fromPerm-spec π xs = refl

    private
      module Unused where
        `⟨0↔1+_⟩ : ∀ {n} (i : Fin n) → Bij (1 + n)
        `⟨0↔1+ i ⟩ = fromPerm P.`⟨0↔1+ i ⟩

        `⟨0↔1+_⟩-spec : ∀ {n} (i : Fin n) (xs : Vec A (suc n)) → `⟨0↔1+ i ⟩ · xs ≡ ⟨0↔1+ i ⟩ xs
        `⟨0↔1+ i ⟩-spec xs rewrite sym (P.`⟨0↔1+ i ⟩-spec xs) | fromPerm-spec P.`⟨0↔1+ i ⟩ xs = refl

        `⟨0↔_⟩ : ∀ {n} (i : Fin n) → Bij n
        `⟨0↔ i ⟩ = fromPerm P.`⟨0↔ i ⟩

        `⟨0↔_⟩-spec : ∀ {n} (i : Fin n) (xs : Vec A n) → `⟨0↔ i ⟩ · xs ≡ ⟨0↔ i ⟩ xs
        `⟨0↔ i ⟩-spec xs rewrite sym (P.`⟨0↔ i ⟩-spec xs) | fromPerm-spec P.`⟨0↔ i ⟩ xs = refl

    `⟨_↔_⟩ : ∀ {n} (i j : Fin n) → Bij n
    `⟨ i ↔ j ⟩ = fromPerm P.`⟨ i ↔ j ⟩

    `⟨_↔_⟩-spec : ∀ {n} (i j : Fin n) (xs : Vec A n) → `⟨ i ↔ j ⟩ · xs ≡ ⟨ i ↔ j ⟩ xs
    `⟨ i ↔ j ⟩-spec xs rewrite sym (P.`⟨ i ↔ j ⟩-spec xs) | fromPerm-spec P.`⟨ i ↔ j ⟩ xs = refl
