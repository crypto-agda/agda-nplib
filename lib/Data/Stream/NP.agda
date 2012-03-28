module Data.Stream.NP where

import Level as L
open import Data.Bool
open import Data.Nat
open import Function
open import Data.Empty
open import Function.Equality using (_⟶_)
open import Data.Product using (Σ; _,_; _×_; uncurry; ∃; proj₁; proj₂)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≢_)
open import Relation.Nullary
open import Relation.Binary

not≢id : ∀ b → not b ≢ b
not≢id true  ()
not≢id false ()

not∘not≡id : ∀ b → b ≡ not (not b)
not∘not≡id true  = ≡.refl
not∘not≡id false = ≡.refl

module M1 where
  Stream : Set → Set
  Stream A = ℕ → A

  setoid : Setoid L.zero L.zero → Setoid _ _
  setoid s = record
    { Carrier       = Stream A
    ; _≈_           = λ xs ys → ∀ n → S._≈_ (xs n) (ys n)
    ; isEquivalence = record
      { refl  = λ n → S.refl
      ; sym   = λ p n → S.sym (p n)
      ; trans = λ p q n → S.trans (p n) (q n)
      }
    }
    where module S = Setoid s
          A = S.Carrier

  map : ∀ {A B : Set} → (A → B) → Stream A → Stream B
  map f g x = f (g x)

  diagonal : ∀ {A} → Stream (Stream A) → Stream A
  diagonal f n = f n n

  cantor : Stream (Stream Bool) → Stream Bool
  cantor = map not ∘ diagonal

  _≉_ : ∀ {A} → Stream A → Stream A → Set
  xs ≉ ys = ∃ λ n → xs n ≢ ys n

  cantor-lem : ∀ xss n → cantor xss ≉ xss n
  cantor-lem xss n = n , not≢id _

  _≈_ : ∀ {A} → Stream A → Stream A → Set
  xs ≈ ys = ∀ n → xs n ≡ ys n

  ≉-sound : ∀ {A} {xs ys : Stream A} → xs ≉ ys → ¬(xs ≈ ys)
  ≉-sound (n , p) q = p (q n)

  ≉→≢ : ∀ {A} {xs ys : Stream A} → xs ≉ ys → xs ≢ ys
  ≉→≢ (_ , f) ≡.refl = f ≡.refl

  _∈_ : ∀ {A} → Stream A → Stream (Stream A) → Set
  xs ∈ xss = ∃ λ n → xs ≈ xss n

  _∉_ : ∀ {A} → Stream A → Stream (Stream A) → Set
  xs ∉ xss = ¬(xs ∈ xss)

  cantor-thm : ∀ xss → cantor xss ∉ xss
  cantor-thm xss (n , pn) = proj₂ (cantor-lem xss n) (pn n)

  -- Meaning that their exists a set that is bigger than ℕ.
  -- A nice thing with this statement is that it only involves: Set,→,∀,∃,ℕ,≢(¬(⊥),≡)
  cantor-thm2 : ∃ λ (S : Set) → ∀ (f : ℕ → S) → ∃ λ (e : S) → ∀ n → e ≢ f n
  cantor-thm2 = Stream Bool , (λ f → cantor f , ≉→≢ ∘ cantor-lem f)

  -- Meaning that their exists a set that is bigger than ℕ.
  -- A nice thing with this statement is that it only involves: Set,→,∀,∃,ℕ,≡,⊥
  cantor-thm3 : ∃ λ (S : Set) → ∀ (f : ℕ → S) → ∃ λ (e : S) → ∀ n → e ≡ f n → ⊥
  cantor-thm3 = cantor-thm2

module M2 where
  Stream : Set → Set
  Stream A = ℕ → A

  head : ∀ {A} → Stream A → A
  head f = f zero

  tail : ∀ {A} → Stream A → Stream A
  tail f = f ∘ suc

  map : ∀ {A B : Set} → (A → B) → Stream A → Stream B
  map f g x = f (g x)

  diagonal : ∀ {A} → Stream (Stream A) → Stream A
  -- diagonal xs zero    = head (head xs)
  -- diagonal xs (suc n) = diagonal (tail (map tail xs)) n
  diagonal f n = f n n

  cantor : Stream (Stream Bool) → Stream Bool
  cantor = map not ∘ diagonal

  All : ∀ {A} (P : A → Set) → Stream A → Set
  All P xs = ∀ n → P (xs n)

  Any : ∀ {A} (P : A → Set) → Stream A → Set
  Any P xs = ∃ λ n → P (xs n)

  zipWith : ∀ {A B C : Set} (f : A → B → C) → Stream A → Stream B → Stream C
  -- zipWith f xs ys zero    = f (head xs) (head ys)
  -- zipWith f xs ys (suc n) = zipWith f (tail xs) (tail ys) n
  zipWith f xs ys n = f (xs n) (ys n)

  zip : ∀ {A B : Set} → Stream A → Stream B → Stream (A × B)
  zip = zipWith _,_

  ZipAll : ∀ {A B : Set} (_∼_ : A → B → Set) → Stream A → Stream B → Set
  ZipAll _∼_ xs ys = All (uncurry _∼_) (zip xs ys)

  ZipAny : ∀ {A B : Set} (_∼_ : A → B → Set) → Stream A → Stream B → Set
  ZipAny _∼_ xs ys = Any (uncurry _∼_) (zip xs ys)

  module ZipAllProps {A : Set} (_∼_ : A → A → Set) where
    refl : Reflexive _∼_ → Reflexive (ZipAll _∼_)
    refl re _ = re

    trans : Transitive _∼_ → Transitive (ZipAll _∼_)
    trans tr p q n = tr (p n) (q n)

    sym : Symmetric _∼_ → Symmetric (ZipAll _∼_)
    sym sy p = sy ∘ p

  ZipAll-setoid : Setoid L.zero L.zero → Setoid _ _
  ZipAll-setoid s = record
    { Carrier       = Stream A
    ; _≈_           = ZipAll {A} S._≈_
    ; isEquivalence = record
      { refl  = Z.refl S.refl
      ; sym   = Z.sym S.sym
      ; trans = Z.trans S.trans
      }
    }
    where module S = Setoid s
          A = S.Carrier
          module Z = ZipAllProps S._≈_

  _≉_ : ∀ {A} → Stream A → Stream A → Set
  _≉_ = ZipAny _≢_

  cantor-lem : ∀ xss → All (λ xs → cantor xss ≉ xs) xss
  cantor-lem xss n = n , (not≢id _)

  _≈_ : ∀ {A} → Stream A → Stream A → Set
  _≈_ = ZipAll _≡_

  _∈_ : ∀ {A} → Stream A → Stream (Stream A) → Set
  xs ∈ xss = Any (_≈_ xs) xss

  _∉_ : ∀ {A} → Stream A → Stream (Stream A) → Set
  xs ∉ xss = ¬(xs ∈ xss)

  cantor-thm : ∀ xss → cantor xss ∉ xss
  cantor-thm xss (n , pn) = proj₂ (cantor-lem xss n) (pn n)

{-
  cantor-thm xss zero    = zero , not≢id _
  cantor-thm xss (suc n) = suc {!!} , {!proj₂ hi!}
     where hi : CantorArg (tail xss) (tail xss n)
           hi = cantor-thm (tail xss) n
           hi' : ∃ λ m → {!!} ?
           hi' = hi
-}
{-
open import Data.Unit using (⊤)
import Data.Stream
open import Coinduction
import Function.Related as R

module All {A : Set} (P : A → Set) where
  open Data.Stream using (Stream; _∷_)

  data All : Stream A → Set where
    _∷_ : ∀ {x xs} (px : P x) → ∞ (All (♭ xs)) → All (x ∷ xs)

  head : ∀ {xs} → All xs → P (Data.Stream.head xs)
  head (px ∷ _) = px

  tail : ∀ {xs} → All xs → All (Data.Stream.tail xs)
  tail (_ ∷ pxs) = ♭ pxs

open All using (All; _∷_)

open Data.Stream public

data Any {A : Set} (P : A → Set) : Stream A → Set where
  here  : ∀ {x xs} (px : P x) → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P (♭ xs) → Any P (x ∷ xs)

zip : ∀ {A B : Set} → Stream A → Stream B → Stream (A × B)
zip = zipWith _,_

ZipAll : ∀ {A B : Set} (_∼_ : A → B → Set) → Stream A → Stream B → Set
ZipAll _∼_ xs ys = All (uncurry _∼_) (zip xs ys)

ZipAny : ∀ {A B : Set} (_∼_ : A → B → Set) → Stream A → Stream B → Set
ZipAny _∼_ xs ys = Any (uncurry _∼_) (zip xs ys)

module ZipAllProps {A : Set} (_∼_ : A → A → Set) where
  data ZipAllD {A B : Set} (_∼_ : A → B → Set) : Stream A → Stream B → Set where
    _∷_ : ∀ {x y xs ys} (x∼y : x ∼ y) → ∞ (ZipAllD _∼_ (♭ xs) (♭ ys)) → ZipAllD _∼_ (x ∷ xs) (y ∷ ys)
  →All-uncurry : ∀ {xs ys : Stream A} → ZipAllD _∼_ xs ys → All (uncurry _∼_) (zip xs ys)
  →All-uncurry (x∼y ∷ p) = x∼y ∷ ♯ →All-uncurry (♭ p)

  ←All-uncurry : ∀ {xs ys : Stream A} → All (uncurry _∼_) (zip xs ys) → ZipAllD _∼_ xs ys
  -- ←All-uncurry (x ∷ xs) (y ∷ ys) (px ∷ pxs) = px ∷ ♯ ←All-uncurry (♭ xs) (♭ ys) (♭ pxs)
  ←All-uncurry (px ∷ pxs) = px ∷ ♯ ←All-uncurry (♭ pxs)

  refl : Reflexive _∼_ → Reflexive (ZipAll _∼_)
  refl re {x ∷ xs} = re ∷ ♯ refl re

  trans : Transitive _∼_ → Transitive (ZipAll _∼_)
  trans tr (x∼y ∷ p) (y∼z ∷ q) = tr x∼y y∼z ∷ ♯ trans tr (♭ p) (♭ q)

  sym : Symmetric _∼_ → Symmetric (ZipAll _∼_)
  sym sy (x∼y ∷ p) = sy x∼y ∷ ♯ sym sy (♭ p)

ZipAll-setoid : Setoid L.zero L.zero → Setoid _ _
ZipAll-setoid s = record
  { Carrier       = Stream A
  ; _≈_           = ZipAll {A} S._≈_
  ; isEquivalence = record
    { refl  = Z.refl S.refl
    ; sym   = Z.sym S.sym
    ; trans = Z.trans S.trans
    }
  }
  where module S = Setoid s
        A = S.Carrier
        module Z = ZipAllProps S._≈_

module ≈-Reasoning {A : Set} = Setoid-Reasoning (setoid A)

module M {A : Set} where
  open Setoid (setoid A) public using (refl; trans; sym)
open M public

diagonal : ∀ {A : Set} → Stream (Stream A) → Stream A
diagonal ((x ∷ xs) ∷ xss) = x ∷ ♯ diagonal (map tail (♭ xss))

-- nats = 0 ∷ map suc nats
-- tab f = map f nats
-- diag = map (head ∘ head) ∘ iterate (tail ∘ tail)
-- diag xs = tab (λ i → xs ! i ! i)

cantor : Stream (Stream Bool) → Stream Bool
cantor = map not ∘ diagonal

infix 4 _∈'_

data _∈'_ {A} : Stream A → Stream (Stream A) → Set where
  here  : ∀ {x y xs}   (x≈y  : x ≈ y)     → x ∈' y ∷ xs
  there : ∀ {x y z xs} (x≈y  : x ≈ y) (x∈xs : x ∈' ♭ xs) → y ∈' z ∷ xs

_∉'_ : ∀ {A} (xs : Stream A) (xss : Stream (Stream A)) → Set
xs ∉' xss = ¬(xs ∈' xss)

≈-head : ∀ {A} {x y : A} {xs ys} → x ∷ xs ≈ y ∷ ys → x ≡ y
≈-head (_ ∷ _) = ≡.refl

not∷ : ∀ b bs bs' → ¬(not b ∷ bs ≈ b ∷ bs')
not∷ true  _ _ ()
not∷ false _ _ ()

_>>=_ : ∀ {A B : Set} → Stream A → (A → Stream B) → Stream B
s >>= f = diagonal (map f s)

ap : ∀ {A B : Set} → Stream (A → B) → Stream A → Stream B
ap fs xs = fs >>= λ f →
           xs >>= λ x →
           repeat (f x)

zap : ∀ {A B : Set} → Stream (A → B) → Stream A → Stream B
zap = zipWith id

infix 4 _≋_

_≋_ : ∀ {A} → Stream (Stream A) → Stream (Stream A) → Set
_≋_ = ZipAll _≈_

_≉_ : ∀ {A} → Stream A → Stream A → Set
-- xs ≉ ys = ¬(xs ≈ ys)
_≉_ = ZipAny _≢_

cant-thm : ∀ xss → All (_≉_ (cantor xss)) xss
cant-thm xss = here (not≢id _) ∷ ♯ pf (cant-thm (tail (map tail xss)))
  where
    open R.EquationalReasoning

    infixr 2 _→⟨_⟩_

    _→⟨_⟩_ : ∀ {x y z} (X : Set x) {Y : Set y} {Z : Set z} →
              (X → Y) → (Y → Z) → X → Z
    (X →⟨ X→Y ⟩ Y→Z) x = Y→Z (X→Y x)

    pf =   All (_≉_ (cantor (tail (map tail xss)))) (tail (map tail xss))
         →⟨ _∷_ {!!} ∘ ♯_ ⟩
           All (_≉_ (cantor (tail (map tail xss)))) (map tail xss)
         →⟨ {!All.tail!} ⟩
           All (_≉_ (cantor xss)) (tail xss) ∎

{-
cant-thm ((x ∷ xs) ∷ xs₁) = (not∷ _ _ _) ∷ ♯ {!cant-thm (♭ xs₁)!}

{-
map-cong' : ∀ {A B} (f : Stream A → Stream B) {xs ys} →
           xs ≋ ys → map f xs ≋ map f ys
map-cong' f (x≈ ∷ xs≈) = {!!} ∷ ♯ map-cong' f (♭ xs≈)
-}

tail-cong : ∀ {A} {xs ys : Stream A} → xs ≈ ys → tail xs ≈ tail ys
tail-cong (_ ∷ xs≈) = ♭ xs≈

map-tail-cong' : ∀ {A} {xs ys : Stream (Stream A)} →
           xs ≋ ys → map tail xs ≋ map tail ys
map-tail-cong' (x≈ ∷ xs≈) = tail-cong x≈ ∷ ♯ map-tail-cong' (♭ xs≈)

diagonal-cong : ∀ {A} {xs ys : Stream (Stream A)} →
                  xs ≋ ys → diagonal xs ≈ diagonal ys
diagonal-cong ((x ∷ xs≈) ∷ xss≈) = x ∷ ♯ diagonal-cong (map-tail-cong' (♭ xss≈))

map-tail-repeat : ∀ {A} (xs : Stream A) → map tail (map repeat xs) ≈ map repeat xs
map-tail-repeat (x ∷ xs) = _ ∷ ♯ map-tail-repeat (♭ xs)

-- map not (diag (map tail xss)) = tail (map not (diag xss))

module ≋ {A} = Setoid (ZipAll-setoid (setoid A))

cantor-tail : ∀ (xss : Stream (Stream Bool)) → cantor (map tail (tail xss)) ≈ tail (cantor xss)
cantor-tail ((x ∷ xs) ∷ xs₁) = map-cong not (diagonal-cong (map-tail-cong' ≋.refl))

≈-∈' : ∀ {A : Set} {xs ys : Stream A} {xss} → xs ≈ ys → xs ∈' xss → ys ∈' xss
≈-∈' p (here x≈y) = here (trans (sym p) x≈y)
≈-∈' p (there x≈y q) = there (trans x≈y p) q

module MM where
  cantor-thm : ∀ (xss : Stream (Stream Bool)) → cantor xss ∉' xss
  ∈'-tail : ∀ {xs ys} {xss : Stream (Stream Bool)} → xs ∈' xss → ¬(tail xs ≈ ys)
               -- ys ∈' map tail xss

  cantor-thm ((x ∷ xs) ∷ xss) (here x≈y) = not∷ x _ _ x≈y
  cantor-thm ((x ∷ xs) ∷ xss) (there {._ ∷ ys} (._ ∷ ys≈zs) cs∈xss)
    = ∈'-tail cs∈xss (♭ ys≈zs)
    -- = cantor-thm (map tail (♭ xss)) (∈'-tail cs∈xss (♭ ys≈zs))

  ∈'-tail (here (x ∷ xs≈)) q = {!!}
  ∈'-tail (there (x ∷ xs≈) p) q = {!!}

∈'-tail : ∀ {A : Set} {xs} {xss : Stream (Stream A)} → xs ∈' xss → tail xs ∈' map tail xss
∈'-tail (here (x ∷ xs≈)) = here (♭ xs≈)
∈'-tail (there (x ∷ xs≈) p) = there (♭ xs≈) (∈'-tail p)

--  there : ∀ {x y z xs} (x≈y  : x ≈ y) (x∈xs : x ∈' ♭ xs) → y ∈' z ∷ xs

cantor-thm : ∀ (xss : Stream (Stream Bool)) → cantor xss ∉' xss
cantor-thm ((x ∷ xs) ∷ xss) (here x≈y) = not∷ x _ _ x≈y
cantor-thm ((x ∷ xs) ∷ xss) (there {._ ∷ ys} (._ ∷ ys≈zs) cs∈xss)
  = cantor-thm (map tail (♭ xss)) (≈-∈' (♭ ys≈zs) (∈'-tail cs∈xss))

bu : ∀ {A} {xs : Stream A} {xss : Stream (Stream A)} → xs ∈ xss → ℕ → Set
bu here zero = ⊤
bu here (suc n) = ⊥
bu (there p) zero = ⊥
bu (there p) (suc n) = {!S∈' p n!}

S∈' : ∀ {A} {xs : Stream A} {xss : Stream (Stream A)} → xs ∈' xss → ℕ → Set
S∈' (here _) zero = ⊤
S∈' (here _) (suc n) = ⊥
S∈' (there _ p) zero = ⊥
S∈' (there _ p) (suc n) = S∈' p n

{-
data E : ℕ → ℕ → Set where
  zero : E zero zero
  suc  : ∀ {m n} → E m n → E (suc m) (suc n)
-}

S-tail : ∀ {xs : Stream Bool} {xss} (p : xs ∈' xss) n → S∈' p n → S∈' (∈'-tail p) n
S-tail (here (_ ∷ _)) zero _ = _
S-tail (here _) (suc n) ()
S-tail (there _ _) zero ()
S-tail (there (x ∷ xs≈) p) (suc n) q = S-tail p n q

bar : ∀ {xs ys : Stream Bool} {xss} (pp : xs ≈ ys) (p : xs ∈' xss) n → S∈' p n → S∈' (≈-∈' pp p) n
bar pp p n q = {!!}

cantor-thm' : ∀ (xss : Stream (Stream Bool)) (p : cantor xss ∈' xss) n → S∈' p n → ⊥
cantor-thm' ((x ∷ xs) ∷ xss) (here x≈y) zero _ = not∷ x _ _ x≈y
cantor-thm' ((x ∷ xs) ∷ xss) (here x≈y) (suc _) ()
cantor-thm' ((x ∷ xs) ∷ xss) (there {._ ∷ ys} (._ ∷ ys≈zs) cs∈xss) (suc n) q
  = cantor-thm' (map tail (♭ xss)) (≈-∈' (♭ ys≈zs) (∈'-tail cs∈xss)) n (bar (♭ ys≈zs) _ n (S-tail cs∈xss n q))
cantor-thm' ((x ∷ xs) ∷ xss) (there {._ ∷ ys} (._ ∷ ys≈zs) cs∈xss) zero ()

{-
lem : ∀ {A B : Set} (fs : Stream (A → B)) xs → ap fs xs ≈ zap fs xs
lem (f ∷ fs) (x ∷ xs) -- = trans (f x ∷ ♯ pf) (f x ∷ ♯ lem (♭ fs) (♭ xs))
        = ap (f ∷ fs) (x ∷ xs)
       ≈⟨ refl ⟩
          ((f ∷ fs) >>= λ f' →
          (x ∷ xs) >>= λ x' →
          repeat (f' x'))
       ≈⟨ refl ⟩
          ((f ∷ fs) >>= λ f' →
          diagonal (map (repeat ∘ f') (x ∷ xs)))
       ≈⟨ f x ∷ ♯ diagonal-cong (map-tail-cong' {!pf!}) ⟩
          ((f ∷ fs) >>= ff)
       ≈⟨ refl ⟩
          diagonal (map ff (f ∷ fs))
       ≈⟨ f x ∷ ♯ refl ⟩
          diagonal (ff f ∷ ♯ map ff (♭ fs))
       ≈⟨ f x ∷ ♯ refl ⟩
          diagonal (ff' ∷ ♯ map ff (♭ fs))
       ≈⟨ f x ∷ ♯ refl ⟩
          diagonal (ff'' ∷ ♯ map ff (♭ fs))
       ≈⟨ f x ∷ ♯ refl ⟩
          f x ∷ ♯ diagonal (map tail (map ff (♭ fs)))
       ≈⟨ f x ∷ ♯ pf ⟩
          f x ∷ ♯ ap (♭ fs) (♭ xs)
       ≈⟨ f x ∷ ♯ lem (♭ fs) (♭ xs) ⟩
          f x ∷ ♯ zap (♭ fs) (♭ xs)
       ≈⟨ f x ∷ ♯ refl ⟩
          zap (f ∷ fs) (x ∷ xs)
       ∎
  where
    open ≈-Reasoning
    ff = λ f' → diagonal (repeat (f' x) ∷ ♯ map (repeat ∘ f') (♭ xs))
    ff' = diagonal ((f x ∷ ♯ repeat (f x)) ∷ ♯ map (repeat ∘ f) (♭ xs))
    ff'' = f x ∷ ♯ diagonal (map tail (map (repeat ∘ f) (♭ xs)))
    pf3 = map tail (map ff (♭ fs))
           ≈⟨ {!!} ⟩
          map (tail ∘ ff) (♭ fs)
           ≈⟨ {!!} ⟩
          map ff (♭ fs)
    pf = diagonal (map tail (map ff (♭ fs)))
           ≈⟨ {!pf3!} ⟩
          diagonal (map ff (♭ fs))
           ≈⟨ {!!} ⟩
          ap (♭ fs) (♭ xs)
         ∎
    pf2 = λ f' → diagonal (map (repeat ∘ f') (x ∷ xs))
       ≈⟨ f' x ∷ ♯ refl ⟩
          ff f'
        ∎
-}
-}
-}
