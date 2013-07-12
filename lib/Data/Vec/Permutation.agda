-- NOTE with-K
open import Type hiding (★)
open import Level.NP
open import Function.NP
open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Vec.NP
open import Data.Product hiding (map)
open import Data.Fin using (Fin; zero; suc; inject₁)
open import Relation.Binary.PropositionalEquality

module Data.Vec.Permutation where

-- ⟨0↔1+ i ⟩: Exchange elements at position 0 and 1+i.
⟨0↔1+_⟩ : ∀ {n} (i : Fin n) {a} {A : ★ a} → Vec A (1 + n) → Vec A (1 + n)
⟨0↔1+ zero  ⟩ = 0↔1
⟨0↔1+ suc i ⟩ = 0↔1 ∘ (map-tail ⟨0↔1+ i ⟩) ∘ 0↔1
  {- 0   1   2 3 ... i 1+i ... n
     1   0   2 3 ... i 1+i ... n
     1   1+i 2 3 ... i 0   ... n

     1+i 1   2 3 ... i 0   ... n
   -}

-- ⟨0↔ i ⟩: Exchange elements at position 0 and i.
⟨0↔_⟩ : ∀ {n} (i : Fin n) {a} {A : ★ a} → Vec A n → Vec A n
⟨0↔ zero  ⟩ = id
⟨0↔ suc i ⟩ = ⟨0↔1+ i ⟩

⟨0↔zero⟩ : ∀ {n a} {A : ★ a} → ⟨0↔ zero ⟩ ≗ id {A = Vec A (suc n)}
⟨0↔zero⟩ _ = refl

private
    _² : ∀ {a} {A : ★ a} → Endo (Endo A)
    f ² = f ∘ f

module ⟨↔⟩ {a} (A : ★ a) where

    ⟨_↔_⟩ : ∀ {n} (i j : Fin n) → Vec A n → Vec A n
    ⟨ zero  ↔ j     ⟩ = ⟨0↔ j ⟩
    ⟨ i     ↔ zero  ⟩ = ⟨0↔ i ⟩
    ⟨ suc i ↔ suc j ⟩ = map-tail ⟨ i ↔ j ⟩
-- ⟨ # 0 ↔ # 1 ⟩

    comm : ∀ {n} (i j : Fin n) → ⟨ i ↔ j ⟩ ≗ ⟨ j ↔ i ⟩
    comm zero    zero    _ = refl
    comm zero    (suc _) _ = refl
    comm (suc _) zero    _ = refl
    comm (suc i) (suc j) (x ∷ xs) rewrite comm i j xs = refl

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
    ⟨0↔ zero  ⟩²-cancel _  = refl
    ⟨0↔ suc i ⟩²-cancel xs = ⟨0↔1+ i ⟩²-cancel xs

    ⟨_↔_⟩²-cancel : ∀ {n} (i j : Fin n) → ⟨ i ↔ j ⟩ ² ≗ id
    ⟨ zero  ↔ j     ⟩²-cancel xs = ⟨0↔ j   ⟩²-cancel xs
    ⟨ suc i ↔ zero  ⟩²-cancel xs = ⟨0↔1+ i ⟩²-cancel xs
    ⟨ suc i ↔ suc j ⟩²-cancel xs
      rewrite map-tail∘map-tail ⟨ i ↔ j ⟩ ⟨ i ↔ j ⟩ xs
            | map-tail-≗ _ _ ⟨ i ↔ j ⟩²-cancel xs
            | map-tail-id xs = refl

    lem01maptail2 : ∀ {m n a} {A : ★ a} (f : Vec A m → Vec A n) →
                      0↔1 ∘ map-tail (map-tail f) ∘ 0↔1 ≗ map-tail (map-tail f)
    lem01maptail2 _ (_ ∷ _ ∷ _) = refl

    ↔-refl : ∀ {n} (i : Fin n) → ⟨ i ↔ i ⟩ ≗ id
    ↔-refl zero    _  = refl
    ↔-refl (suc i) xs rewrite map-tail-≗ _ _ (↔-refl i) xs = map-tail-id xs

⟨_↔_⟩ : ∀ {n} (i j : Fin n) {a} {A : ★ a} → Vec A n → Vec A n
⟨_↔_⟩ i j = ⟨↔⟩.⟨_↔_⟩ _ i j

module PermutationSyntax where
    infixr 1 _`⁏_
    data Perm : ℕ → ★₀ where
      `id : ∀ {n} → Perm n
      `0↔1 : ∀ {n} → Perm (2 + n)
      _`⁏_ : ∀ {n} → Perm n → Perm n → Perm n
      `tl : ∀ {n} → Perm n → Perm (1 + n)

    _⁻¹ : ∀ {n} → Endo (Perm n)
    `id ⁻¹ = `id
    (f₀ `⁏ f₁) ⁻¹ = f₁ ⁻¹ `⁏ f₀ ⁻¹
    `0↔1 ⁻¹ = `0↔1
    (`tl f) ⁻¹ = `tl (f ⁻¹)

    `⟨0↔1+_⟩ : ∀ {n} (i : Fin n) → Perm (1 + n)
    `⟨0↔1+ zero  ⟩ = `0↔1
    `⟨0↔1+ suc i ⟩ = `0↔1 `⁏ `tl `⟨0↔1+ i ⟩ `⁏ `0↔1

    `⟨0↔_⟩ : ∀ {n} (i : Fin n) → Perm n
    `⟨0↔ zero  ⟩ = `id
    `⟨0↔ suc i ⟩ = `⟨0↔1+ i ⟩

    `⟨_↔_⟩ : ∀ {n} (i j : Fin n) → Perm n
    `⟨ zero  ↔ j     ⟩ = `⟨0↔ j ⟩
    `⟨ i     ↔ zero  ⟩ = `⟨0↔ i ⟩
    `⟨ suc i ↔ suc j ⟩ = `tl `⟨ i ↔ j ⟩

module PermutationSemantics {a} {A : ★ a} where
    open PermutationSyntax

    eval : ∀ {n} → Perm n → Endo (Vec A n)
    eval `id      = id
    eval (f `⁏ g)  = eval g ∘ eval f
    eval `0↔1     = 0↔1
    eval (`tl f)  = λ xs → head xs ∷ eval f (tail xs)

    infixr 9 _·_
    _·_ : ∀ {n} → Perm n → Endo (Vec A n)
    _·_ = eval

    `⟨0↔1+_⟩-spec : ∀ {n} (i : Fin n) (xs : Vec A (suc n)) → `⟨0↔1+ i ⟩ · xs ≡ ⟨0↔1+ i ⟩ xs
    `⟨0↔1+ zero  ⟩-spec xs = refl
    `⟨0↔1+ suc i ⟩-spec (x ∷ y ∷ xs) rewrite `⟨0↔1+ i ⟩-spec (x ∷ xs) = refl

    `⟨0↔_⟩-spec : ∀ {n} (i : Fin n) (xs : Vec A n) → `⟨0↔ i ⟩ · xs ≡ ⟨0↔ i ⟩ xs
    `⟨0↔ zero  ⟩-spec xs = refl
    `⟨0↔ suc i ⟩-spec xs = `⟨0↔1+ i ⟩-spec xs

    _≗′_ : ∀ {n} → Perm n → Perm n → ★ _
    f ≗′ g = ∀ xs → f · xs ≡ g · xs

    open ⟨↔⟩ A hiding (⟨_↔_⟩)

    _⁻¹-inverse : ∀ {n} (f : Perm n) → (f `⁏ f ⁻¹) ≗′ `id
    (`id ⁻¹-inverse) xs = refl
    ((f `⁏ g) ⁻¹-inverse) xs
      rewrite (g ⁻¹-inverse) (f · xs)
            | (f ⁻¹-inverse) xs = refl
    (`0↔1 ⁻¹-inverse) xs = 0↔1²-cancel xs
    ((`tl f) ⁻¹-inverse) (x ∷ xs)
      rewrite (f ⁻¹-inverse) xs = refl

    _⁻¹-involutive : ∀ {n} (f : Perm n) → (f ⁻¹) ⁻¹ ≗′ f
    (`id ⁻¹-involutive) _ = refl
    ((f `⁏ g) ⁻¹-involutive) x
      rewrite (f ⁻¹-involutive) x
            | (g ⁻¹-involutive) (f · x) = refl
    (`0↔1 ⁻¹-involutive) _ = refl
    ((`tl f) ⁻¹-involutive) (x ∷ xs)
      rewrite (f ⁻¹-involutive) xs
            = refl

    _⁻¹-inverse′ : ∀ {n} (f : Perm n) → (f ⁻¹ `⁏ f) ≗′ `id
    (f ⁻¹-inverse′) xs with ((f ⁻¹) ⁻¹-inverse) xs
    ... | p rewrite (f ⁻¹-involutive) (f ⁻¹ · xs) = p

    `⟨_↔_⟩-spec : ∀ {n} (i j : Fin n) (xs : Vec A n) → `⟨ i ↔ j ⟩ · xs ≡ ⟨ i ↔ j ⟩ xs
    `⟨_↔_⟩-spec zero    j       xs = `⟨0↔   j ⟩-spec xs
    `⟨_↔_⟩-spec (suc i) zero    xs = `⟨0↔1+ i ⟩-spec xs
    `⟨_↔_⟩-spec (suc i) (suc j) (x ∷ xs)
       rewrite `⟨ i ↔ j ⟩-spec xs = refl

module PermutationProperties {a : Level} where
    open PermutationSyntax
    open PermutationSemantics

    ⊛-dist-· : ∀ {n} {A : ★ a} (fs : Vec (Endo A) n) (f : Perm n) xs → (f · fs ⊛ f · xs) ≡ f · (fs ⊛ xs)
    ⊛-dist-· _       `id        _  = refl
    ⊛-dist-· fs      `0↔1       xs = ⊛-dist-0↔1 fs xs
    ⊛-dist-· (_ ∷ fs) (`tl f)   (_ ∷ xs) rewrite ⊛-dist-· fs f xs = refl
    ⊛-dist-· fs       (f `⁏ g)   xs rewrite ⊛-dist-· (f · fs) g (f · xs)
                                         | ⊛-dist-· fs f xs = refl

    ·-replicate : ∀ {n} {A : ★ a} (x : A) (f : Perm n) → f · replicate x ≡ replicate x
    ·-replicate x `id = refl
    ·-replicate x `0↔1 = refl
    ·-replicate x (`tl f) rewrite ·-replicate x f = refl
    ·-replicate x (f `⁏ g) rewrite ·-replicate x f | ·-replicate x g = refl

    private
        lem : ∀ {n} {A : ★ a} (fs : Vec (Endo A) n) f xs
              → fs ⊛ f · xs ≡ f · (f ⁻¹ · fs ⊛ xs)
        lem fs f xs rewrite sym (⊛-dist-· (f ⁻¹ · fs) f xs) | (f ⁻¹-inverse′) fs = refl

    ·-map : ∀ {n} {A : ★ a} (f : Endo A) g (xs : Vec A n) → map f (g · xs) ≡ g · map f xs
    ·-map f g xs rewrite sym (⊛-dist-· (replicate f) g xs) | ·-replicate f g = refl

sum-∷ʳ : ∀ {n} x (xs : Vec ℕ n) → sum (xs ∷ʳ x) ≡ sum xs + x
sum-∷ʳ x [] = ℕ°.+-comm x 0
sum-∷ʳ x (x₁ ∷ xs) rewrite sum-∷ʳ x xs | ℕ°.+-assoc x₁ (sum xs) x = refl

rot₁ : ∀ {n a} {A : ★ a} → Vec A n → Vec A n
rot₁ []       = []
rot₁ (x ∷ xs) = xs ∷ʳ x

rot : ∀ {n a} {A : ★ a} → ℕ → Vec A n → Vec A n
rot zero    xs = xs
rot (suc n) xs = rot n (rot₁ xs)

sum-distribˡ : ∀ {A : ★₀} {n} f k (xs : Vec A n) → sum (map (λ x → k * f x) xs) ≡ k * sum (map f xs)
sum-distribˡ f k [] = ℕ°.*-comm 0 k
sum-distribˡ f k (x ∷ xs) rewrite sum-distribˡ f k xs = sym (proj₁ ℕ°.distrib k _ _)

sum-linear : ∀ {A : ★₀} {n} f g (xs : Vec A n) → sum (map (λ x → f x + g x) xs) ≡ sum (map f xs) + sum (map g xs)
sum-linear f g [] = refl
sum-linear f g (x ∷ xs) rewrite sum-linear f g xs = +-interchange (f x) (g x) (sum (map f xs)) (sum (map g xs))

sum-mono : ∀ {A : ★₀} {n f g} (mono : ∀ x → f x ≤ g x)(xs : Vec A n) → sum (map f xs) ≤ sum (map g xs)
sum-mono f≤°g [] = Data.Nat.NP.z≤n
sum-mono f≤°g (x ∷ xs) = f≤°g x +-mono sum-mono f≤°g xs

sum-rot₁ : ∀ {n} (xs : Vec ℕ n) → sum xs ≡ sum (rot₁ xs)
sum-rot₁ [] = refl
sum-rot₁ (x ∷ xs) rewrite sum-∷ʳ x xs = ℕ°.+-comm x _

map-∷ʳ : ∀ {n a} {A : ★ a} (f : A → ℕ) x (xs : Vec A n) → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
map-∷ʳ f x [] = refl
map-∷ʳ f x (x₁ ∷ xs) rewrite map-∷ʳ f x xs = refl

sum-map-rot₁ : ∀ {n a} {A : ★ a} (f : A → ℕ) (xs : Vec A n) → sum (map f (rot₁ xs)) ≡ sum (map f xs)
sum-map-rot₁ f [] = refl
sum-map-rot₁ f (x ∷ xs) rewrite ℕ°.+-comm (f x) (sum (map f xs))
                              | sym (sum-∷ʳ (f x) (map f xs))
                              | sym (map-∷ʳ f x xs)
                              = refl

private
  module Unused where
    module Foo where
    {-
       WRONG
        ⟨_↔_⟩ : ∀ {n} (i j : Fin n) {a} {A : ★ a} → Vec A n → Vec A n
        ⟨ i ↔ j ⟩ = ⟨0↔ i ⟩ ∘ ⟨0↔ j ⟩ ∘ ⟨0↔ i ⟩

        ⟨0↔⟩-spec : ∀ {n a} {A : ★ a} (i : Fin (suc n)) → ⟨0↔ i ⟩ ≗ ⟨ zero ↔ i ⟩ {A = A}
        ⟨0↔⟩-spec _ _ = ≡.refl
        -}

    ⟨0↔_⟩′ : ∀ {n} (i : Fin n) {a} {A : ★ a} → Vec A n → Vec A n
    ⟨0↔_⟩′ {zero}  i xs = xs
    ⟨0↔_⟩′ {suc n} i xs = lookup i xs ∷ tail (xs [ i ]≔ head xs)

    -- ⟨ i ↔+1⟩: Exchange elements at position i and i + 1.
    ⟨_↔+1⟩ : ∀ {n} (i : Fin n) {a} {A : ★ a} → Vec A n → Vec A n
    ⟨ zero  ↔+1⟩ = 0↔1
    ⟨ suc i ↔+1⟩ = map-tail ⟨ i ↔+1⟩

    ⟨↔+1⟩-spec : ∀ {n} (i : Fin n) {a} {A : ★ a} → ⟨ inject₁ i ↔+1⟩ ≗ ⟨ inject₁ i ↔ suc i ⟩ {A = A}
    ⟨↔+1⟩-spec zero    xs       rewrite map-tail-id (0↔1 xs) = refl
    ⟨↔+1⟩-spec (suc i) (x ∷ xs) rewrite ⟨↔+1⟩-spec i xs = refl

    -- rot-up-to i (x₀ ∷ x₁ ∷ x₂ ∷ … ∷ xᵢ ∷ xs)
    --           ≡ (x₁ ∷ x₂ ∷ x₃ ∷ … ∷ x₀ ∷ xs)
    rot-up-to : ∀ {n} (i : Fin n) {a} {A : ★ a} → Vec A n → Vec A n
    rot-up-to zero    = id
    rot-up-to (suc i) = map-tail (rot-up-to i) ∘ 0↔1

    -- Inverse of rot-up-to
    rot⁻¹-up-to : ∀ {n} (i : Fin n) {a} {A : ★ a} → Vec A n → Vec A n
    rot⁻¹-up-to zero    = id
    rot⁻¹-up-to (suc i) = 0↔1 ∘ map-tail (rot⁻¹-up-to i)

    rot⁻¹-up-to∘rot-up-to : ∀ {n} (i : Fin n) {a} {A : ★ a} → rot⁻¹-up-to i ∘ rot-up-to i ≗ id {a} {Vec A n}
    rot⁻¹-up-to∘rot-up-to zero            _ = refl
    rot⁻¹-up-to∘rot-up-to (suc i) {A = A} (x₀ ∷ []) rewrite rot⁻¹-up-to∘rot-up-to i {A = A} [] = refl
    rot⁻¹-up-to∘rot-up-to (suc i)         (x₀ ∷ x₁ ∷ xs) rewrite rot⁻¹-up-to∘rot-up-to i (x₀ ∷ xs) = refl
