{-# OPTIONS --without-K #-}
module Data.Tree.Binary.Perfect where

open import Function
open import Data.Two
open import Data.Nat.NP
open import Data.Product hiding (map; swap)
open import Data.Vec  hiding (map; replicate; lookup; last; _∈_; module _∈_)
open import Data.Bits hiding (map; replicate)
open import Relation.Binary.PropositionalEquality.NP

data Tree {a} (A : Set a) : ℕ → Set a where
  leaf : (x : A) → Tree A zero
  fork : ∀ {n} (left right : Tree A n) → Tree A (suc n)

data _∈_ {a}{A : Set a}(x : A) : {n : ℕ} → Tree A n → Set a where
  here  : x ∈ leaf x
  left  : {n : ℕ}{t₁ t₂ : Tree A n} → x ∈ t₁ → x ∈ fork t₁ t₂
  right : {n : ℕ}{t₁ t₂ : Tree A n} → x ∈ t₂ → x ∈ fork t₁ t₂

_=<<_ : ∀ {n m a b} {A : Set a} {B : Set b}
        → (A → Tree B m) → Tree A n → Tree B (n + m)
f =<< leaf x   = f x
f =<< fork t u = fork (f =<< t) (f =<< u)

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → Tree A n → Tree B n
map f (leaf x)   = leaf (f x)
map f (fork t u) = fork (map f t) (map f u)
-- This one has type Tree B (n + 0)
-- map f t = (leaf ∘ f) =<< t

module _ {a} {A : Set a} where

    leaf= : {x y : A} → x ≡ y → leaf x ≡ leaf y
    leaf= = ap leaf

    fork= : ∀ {n} {x y u v : Tree A n} → x ≡ y → u ≡ v → fork x u ≡ fork y v
    fork= = ap₂ fork

    replicate : ∀ n → A → Tree A n
    replicate zero    x = leaf x
    replicate (suc n) x = fork t t where t = replicate n x

    from-fun : ∀ {n} → (Bits n → A) → Tree A n
    from-fun {zero}  f = leaf (f [])
    from-fun {suc n} f = fork (from-fun (f ∘ 0∷_)) (from-fun (f ∘ 1∷_))

    to-fun : ∀ {n} → Tree A n → Bits n → A
    to-fun (leaf x)    _        = x
    to-fun (fork t₀ t₁) (b ∷ bs) = to-fun ([0: t₀ 1: t₁ ] b) bs

    to-fun∘from-fun : ∀ {n} (f : Bits n → A) → to-fun (from-fun f) ≗ f
    to-fun∘from-fun {zero}  f [] = refl
    to-fun∘from-fun {suc n} f (0∷ xs) = to-fun∘from-fun (f ∘ 0∷_) xs
    to-fun∘from-fun {suc n} f (1∷ xs) = to-fun∘from-fun (f ∘ 1∷_) xs

    from-fun∘to-fun : ∀ {n} (t : Tree A n) → from-fun (to-fun t) ≡ t
    from-fun∘to-fun (leaf x) = refl
    from-fun∘to-fun (fork t₀ t₁)
      = fork= (from-fun∘to-fun t₀) (from-fun∘to-fun t₁)

    to-fun→from-fun : ∀ {n} (t : Tree A n) (f : Bits n → A) → to-fun t ≗ f → t ≡ from-fun f
    to-fun→from-fun (leaf x) f t≗f = leaf= (t≗f [])
    to-fun→from-fun (fork t₀ t₁) f t≗f =
      fork= (to-fun→from-fun t₀ _ (t≗f ∘ 0∷_))
            (to-fun→from-fun t₁ _ (t≗f ∘ 1∷_))

    from-fun→to-fun : ∀ {n} (t : Tree A n) (f : Bits n → A) → t ≡ from-fun f → to-fun t ≗ f
    from-fun→to-fun ._ _ refl = to-fun∘from-fun _

    from-fun-≗ : ∀ {n} {f g : Bits n → A} → f ≗ g → from-fun f ≡ from-fun g
    from-fun-≗ {zero}  f≗g = leaf= (f≗g [])
    from-fun-≗ {suc n} f≗g =
      fork= (from-fun-≗ (f≗g ∘ 0∷_))
            (from-fun-≗ (f≗g ∘ 1∷_))

    lookup : ∀ {n} → Bits n → Tree A n → A
    lookup = flip to-fun

    get-left : ∀ {n} → Tree A (1 + n) → Tree A n
    get-left (fork t _) = t

    get-right : ∀ {n} → Tree A (1 + n) → Tree A n
    get-right (fork _ t) = t

    ηfork : ∀ {n} (t : Tree A (1 + n)) → t ≡ fork (get-left t) (get-right t)
    ηfork (fork _ _) = refl

    Prod : ℕ → Set a
    Prod zero    = A
    Prod (suc n) = Prod n × Prod n

    to-Prod : ∀ {n} → Tree A n →  Prod n
    to-Prod (leaf x)   = x
    to-Prod (fork t u) = to-Prod t , to-Prod u

    from-Prod : ∀ {n} → Prod n → Tree A n
    from-Prod {zero}  x       = leaf x
    from-Prod {suc n} (x , y) = fork (from-Prod x) (from-Prod y)

    from-× : A × A → Tree A 1
    from-× = from-Prod

    to-× : Tree A 1 → A × A
    to-× = to-Prod

    swap : ∀ {n} → Tree A (1 + n) → Tree A (1 + n)
    swap t = fork (get-right t) (get-left t)

    map-inner : ∀ {n} → (Tree A (1 + n) → Tree A (1 + n)) → (Tree A (2 + n) → Tree A (2 + n))
    map-inner f (fork (fork t₀ t₁) (fork t₂ t₃)) =
      case f (fork t₁ t₂) of λ { (fork t₄ t₅) → fork (fork t₀ t₄) (fork t₅ t₃) }

    map-outer : ∀ {n} → (f g : Tree A n → Tree A n) → (Tree A (1 + n) → Tree A (1 + n))
    map-outer f g (fork t u) = fork (f t) (g u)

    interchange : ∀ {n} → Tree A (2 + n) → Tree A (2 + n)
    interchange = map-inner swap

    inner : ∀ {n} → Tree A (2 + n) → Tree A (1 + n)
    inner t = fork (get-right (get-left t)) (get-left (get-right t))

    first : ∀ {n} → Tree A n → A
    first (leaf x)   = x
    first (fork t _) = first t

    last : ∀ {n} → Tree A n → A
    last (leaf x)   = x
    last (fork _ t) = last t

    -- Returns the flat vector of leaves underlying the perfect binary tree.
    to-vec : ∀ {n} → Tree A n → Vec A (2^ n)
    to-vec (leaf x)    = x ∷ []
    to-vec (fork t₀ t₁) = to-vec t₀ ++ to-vec t₁

    from-vec : ∀ {n} → Vec A (2^ n) → Tree A n
    from-vec {zero}  (x ∷ []) = leaf x
    from-vec {suc n} v        = fork (from-vec (take _ v))
                                     (from-vec (drop (2^ n) v))

    lookup' : ∀ {m n} → Bits m → Tree A (m + n) → Tree A n
    lookup' [] t = t
    lookup' (b ∷ bs) (fork t₀ t₁) = lookup' bs ([0: t₀ 1: t₁ ] b)

    update' : ∀ {m n} → Bits m → Tree A n → Tree A (m + n) → Tree A (m + n)
    update' []        val t = val
    update' (b ∷ key) val (fork t₀ t₁)
      = fork ([0: update' key val t₀ 1: t₀ ] b)
             ([0: t₁ 1: update' key val t₁ ] b)

    ∈-to-bits : ∀ {x n} {t : Tree A n} → x ∈ t → Bits n
    ∈-to-bits here = []
    ∈-to-bits (left key)  = 0∷ ∈-to-bits key
    ∈-to-bits (right key) = 1∷ ∈-to-bits key

    ∈-lookup : ∀ {x n} {t : Tree A n} (path : x ∈ t) → lookup (∈-to-bits path) t ≡ x
    ∈-lookup here = refl
    ∈-lookup (left path)  = ∈-lookup path
    ∈-lookup (right path) = ∈-lookup path

    lookup-∈ : ∀ {n} key (t : Tree A n) → lookup key t ∈ t
    lookup-∈ [] (leaf x) = here
    lookup-∈ (0∷ key) (fork t₀ t₁) = left  (lookup-∈ key t₀)
    lookup-∈ (1∷ key) (fork t₀ t₁) = right (lookup-∈ key t₁)
-- -}
-- -}
-- -}
-- -}
-- -}
