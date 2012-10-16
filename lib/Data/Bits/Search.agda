open import Data.Nat.NP hiding (_==_) renaming (_<=_ to _ℕ<=_)
open import Data.Bits
open import Data.Bool.Properties using (not-involutive)
import Data.Vec.NP as V
open V hiding (rewire; rewireTbl; sum) renaming (map to vmap; swap to vswap)

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡
open import Function.NP hiding (_→⟨_⟩_)
open import Algebra.FunctionProperties.NP

module Data.Bits.Search where
module Search {i} {I : Set i} (`1 : I) (`2*_ : I → I)
              {a} {A : I → Set a} (_∙_ : ∀ {m} → A m → A m → A (`2* m)) where

  `2^_ : ℕ → I
  `2^_ = fold `1 `2*_

  search : ∀ {n} → (Bits n → A `1) → A (`2^ n)
  search {zero}  f = f []
  search {suc n} f = search (f ∘ 0∷_) ∙ search (f ∘ 1∷_)

  searchBit : (Bit → A `1) → A (`2* `1)
  searchBit f = f 0b ∙ f 1b

  -- search-ext
  search-≗ : ∀ {n} (f g : Bits n → A `1) → f ≗ g → search f ≡ search g
  search-≗ {zero}  f g f≗g = f≗g []
  search-≗ {suc n} f g f≗g
    rewrite search-≗ (f ∘ 0∷_) (g ∘ 0∷_) (f≗g ∘ 0∷_)
          | search-≗ (f ∘ 1∷_) (g ∘ 1∷_) (f≗g ∘ 1∷_) = refl

  module Comm (∙-comm : ∀ {m} (x y : A m) → x ∙ y ≡ y ∙ x) where

    {- This pad bit vector allows to specify which bit do we negate in the vector. -}
    search-comm : ∀ {n} (pad : Bits n) (f : Bits n → A `1) → search f ≡ search (f ∘ _⊕_ pad)
    search-comm {zero} pad f = refl
    search-comm {suc n} (b ∷ pad) f
      rewrite search-comm pad (f ∘ 0∷_)
              | search-comm pad (f ∘ 1∷_)
      with b
    ... | true  = ∙-comm (search (f ∘ 0∷_ ∘ _⊕_ pad)) _
    ... | false = refl
  open Comm public

module SimpleSearch {a} {A : Set a} (_∙_ : A → A → A) where

    open Search 1 2*_ {A = const A} _∙_ public

    module SearchUnit ε (ε∙ε : ε ∙ ε ≡ ε) where
        search-constε≡ε : ∀ n → search {n = n} (const ε) ≡ ε
        search-constε≡ε zero = refl
        search-constε≡ε (suc n) rewrite search-constε≡ε n = ε∙ε

    searchBit-search : ∀ n (f : Bits (suc n) → A) → searchBit (λ b → search (f ∘ _∷_ b)) ≡ search f
    searchBit-search n f = refl

    search-≗₂ : ∀ {m n} (f g : Bits m → Bits n → A) → f ≗₂ g
                  → search (search ∘ f) ≡ search (search ∘ g)
    search-≗₂ f g f≗g = search-≗ (search ∘ f) (search ∘ g) (λ xs →
                          search-≗ (f xs) (g xs) (λ ys →
                            f≗g xs ys))

    search-+ : ∀ {m n} (f : Bits (m + n) → A) →
                 search {m + n} f
               ≡ search {m} (λ xs → search {n} (λ ys → f (xs ++ ys)))
    search-+ {zero} f = refl
    search-+ {suc m} f rewrite search-+ {m} (f ∘ 0∷_)
                             | search-+ {m} (f ∘ 1∷_) = refl

    module SearchInterchange (∙-interchange : Interchange _≡_ _∙_ _∙_) where

        search-dist : ∀ {n} (f₀ f₁ : Bits n → A) → search (λ x → f₀ x ∙ f₁ x) ≡ search f₀ ∙ search f₁
        search-dist {zero}  _ _ = refl
        search-dist {suc n} f₀ f₁
          rewrite search-dist (f₀ ∘ 0∷_) (f₁ ∘ 0∷_)
                | search-dist (f₀ ∘ 1∷_) (f₁ ∘ 1∷_)
                = ∙-interchange _ _ _ _

        search-searchBit : ∀ {n} (f : Bits (suc n) → A) →
                             search (λ xs → searchBit (λ b → f (b ∷ xs))) ≡ search f
        search-searchBit f = search-dist (f ∘ 0∷_) (f ∘ 1∷_)

        search-search : ∀ {m n} (f : Bits (m + n) → A) →
                          search {m} (λ xs → search {n} (λ ys → f (xs ++ ys)))
                        ≡ search {n} (λ ys → search {m} (λ xs → f (xs ++ ys)))
        search-search {zero} f = refl
        search-search {suc m} {n} f
          rewrite search-search {m} {n} (f ∘ 0∷_)
                | search-search {m} {n} (f ∘ 1∷_)
                | search-searchBit {n} (λ { (b ∷ ys) → search {m} (λ xs → f (b ∷ xs ++ ys)) })
                = refl
        {- -- It might also be done by using search-dist twice and commutativity of addition.
           -- However, this also affect 'f' and makes this proof actually longer.
           search-search {m} {n} f =
                             search {m} (λ xs → search {n} (λ ys → f (xs ++ ys)))
                           ≡⟨ {!!} ⟩
                             search {m + n} f
                           ≡⟨ {!!} ⟩
                             search {n + m} (f ∘ vswap n)
                           ≡⟨ {!!} ⟩
                             search {n} (λ ys → search {m} (λ xs → f (vswap n (ys ++ xs))))
                           ≡⟨ {!!} ⟩
                             search {n} (λ ys → search {m} (λ xs → f (xs ++ ys)))
                           ∎
                           where open ≡-Reasoning
         -}

        search-swap : ∀ {m n} (f : Bits (m + n) → A) → search {n + m} (f ∘ vswap n) ≡ search {m + n} f
        search-swap {m} {n} f =
                     search {n + m} (f ∘ vswap n)
                   ≡⟨ search-+ {n} {m} (f ∘ vswap n) ⟩
                     search {n} (λ ys → search {m} (λ xs → f (vswap n (ys ++ xs))))
                   ≡⟨ search-≗₂ {n} {m}
                                (λ ys → f ∘ vswap n ∘ _++_ ys)
                                (λ ys → f ∘ flip _++_ ys)
                                (λ ys xs → cong f (swap-++ n ys xs)) ⟩
                     search {n} (λ ys → search {m} (λ xs → f (xs ++ ys)))
                   ≡⟨ sym (search-search {m} {n} f) ⟩
                     search {m} (λ xs → search {n} (λ ys → f (xs ++ ys)))
                   ≡⟨ sym (search-+ {m} {n} f) ⟩
                     search {m + n} f
                   ∎ where open ≡-Reasoning

        search-0↔1 : ∀ {n} (f : Bits n → A) → search {n} (f ∘ 0↔1) ≡ search {n} f
        search-0↔1 {zero}        _ = refl
        search-0↔1 {suc zero}    _ = refl
        search-0↔1 {suc (suc n)} _ = ∙-interchange _ _ _ _

    module Bij (∙-comm : Commutative _≡_ _∙_)
              (∙-interchange : Interchange _≡_ _∙_ _∙_) where
        open SearchInterchange ∙-interchange using (search-0↔1)
        open import Data.Bits.OperationSyntax hiding (_∙_)
        search-bij : ∀ {n} f (g : Bits n → A) → search (g ∘ eval f) ≡ search g
        search-bij `id     _ = refl
        search-bij `0↔1    f = search-0↔1 f
        search-bij (f `⁏ g) h
          rewrite search-bij f (h ∘ eval g)
                | search-bij g h
                = refl
        search-bij {suc n} (`id   `∷ f) g
          rewrite search-bij (f 0b) (g ∘ 0∷_)
                | search-bij (f 1b) (g ∘ 1∷_)
                = refl
        search-bij {suc n} (`notᴮ `∷ f) g
          rewrite search-bij (f 1b) (g ∘ 0∷_)
                | search-bij (f 0b) (g ∘ 1∷_)
                = ∙-comm _ _

|de-morgan| : ∀ {n} (f g : Bits n → Bit) → f |∨| g ≗ not ∘ ((not ∘ f) |∧| (not ∘ g))
|de-morgan| f g x with f x
... | true = refl
... | false = sym (not-involutive _)

open SimpleSearch

search-de-morgan : ∀ {n} op (f g : Bits n → Bit) →
                   search op (f |∨| g) ≡ search op (not ∘ ((not ∘ f) |∧| (not ∘ g)))
search-de-morgan op f g = search-≗ op _ _ (|de-morgan| f g)

search-hom :
  ∀ {n a b}
    {A : Set a} {B : Set b}
    (_+_ : A → A → A)
    (_*_ : B → B → B)
    (f : A → B)
    (p : Bits n → A)
    (hom : ∀ x y → f (x + y) ≡ f x * f y)
    → f (search _+_ p) ≡ search _*_ (f ∘ p)
search-hom {zero}  _   _   _ _ _   = refl
search-hom {suc n} _+_ _*_ f p hom =
   trans (hom _ _)
         (cong₂ _*_ (search-hom _+_ _*_ f (p ∘ 0∷_) hom)
                    (search-hom _+_ _*_ f (p ∘ 1∷_) hom))
