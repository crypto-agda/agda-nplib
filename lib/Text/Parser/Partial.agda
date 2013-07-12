{-# OPTIONS --without-K #-}
open import Type
open import Data.Maybe.NP as Maybe
open import Data.Nat
open import Data.One
open import Data.Char renaming (_==_ to _==ᶜ_)
open import Data.String as String
open import Data.List as L using (List; []; _∷_; null; filter)
open import Data.Product.NP hiding (map)
open import Data.Bool
open import Function
open import Coinduction
import Level as L
import Category.Monad as Cat
import Category.Monad.Partiality.NP as Pa
open   Pa using (_⊥; run_for_steps?; now; later; never; _∘⊥_; module M⊥)

module Text.Parser.Partial where

open M? L.zero using () renaming (_=<<_ to _=<<?_; _⊛_ to _⊛?_; join to join?)
open M⊥ L.zero using () renaming (_=<<_ to _=<<⊥_; _⊛_ to _⊛⊥_; _>>=_ to _>>=⊥_; _<$>_ to map⊥)

Parser⊥ : ★ → ★
Parser⊥ A = List Char → (Maybe (A × List Char))⊥

pure : ∀ {A} → A → Parser⊥ A
pure a s = now (just (a , s))

infixr 3 _⟨|⟩_
_⟨|⟩_ : ∀ {A} → (f g : Parser⊥ A) → Parser⊥ A
_⟨|⟩_ f g s = maybe′ (now ∘ just) (g s) =<<⊥ f s

empty : ∀ {A} → Parser⊥ A
empty _ = now nothing

sat : (Char → Bool) → Parser⊥ Char
sat pred (x ∷ xs) = (if pred x then pure x else empty) xs
sat _    []       = now nothing

eof : Parser⊥ 𝟙
eof s = if null s then pure _ [] else empty []

parser∞ : ∀ {A} → ∞(Parser⊥ A) → Parser⊥ A
parser∞ p s = later (♯ (♭ p) s)

parser⊥ : ∀ {A} → (Parser⊥ A)⊥ → Parser⊥ A
parser⊥ (now p)   s = p s
parser⊥ (later p) s = later (♯ parser⊥ (♭ p) s)

-- The remaning input is dropped, you may want to first
-- combine your parser `p' with `eof': `p <* eof'
runParser : ∀ {A} → Parser⊥ A → List Char → (Maybe A)⊥
runParser p s = (map⊥ ∘ map?) proj₁ (p s)

infixr 0 _>>=_
_>>=_ : ∀ {A B} → Parser⊥ A → (A → Parser⊥ B) → Parser⊥ B
_>>=_ pa f = maybe′ (uncurry f) (now nothing) ∘⊥ pa

infixl 0 _=<<_
_=<<_ : ∀ {A B} → (A → Parser⊥ B) → Parser⊥ A → Parser⊥ B
_=<<_ f pa = pa >>= f

join : ∀ {A} → Parser⊥ (Parser⊥ A) → Parser⊥ A
join = _=<<_ id

map : ∀ {A B} → (A → B) → Parser⊥ A → Parser⊥ B
map f pa = pa >>= pure ∘ f

infixl 4 _⊛_ _*>_ _<*_
_⊛_ : ∀ {A B} → Parser⊥ (A → B) → Parser⊥ A → Parser⊥ B
_⊛_ pf pa = pf >>= λ f → pa >>= λ a → pure (f a)

_*>_ : ∀ {A B} → Parser⊥ A → Parser⊥ B → Parser⊥ B
p₁ *> p₂ = p₁ >>= const p₂

_<*_ : ∀ {A B} → Parser⊥ A → Parser⊥ B → Parser⊥ A
p₁ <* p₂ = p₁ >>= λ x → p₂ *> pure x

choices : ∀ {A} → List (Parser⊥ A) → Parser⊥ A
choices = L.foldr _⟨|⟩_ empty

{-
mutual
  many : ∀ {A} → Parser⊥ A → Parser⊥ (List A)
  many p = some p ⟨|⟩ pure []

  some : ∀ {A} → Parser⊥ A → Parser⊥ (List A)
  some p = pure _∷_ ⊛ p ⊛ many p
-}

char : Char → Parser⊥ 𝟙
char c = sat (_==ᶜ_ c) *> pure _

private
  notElem : Char → List Char → Bool
  notElem c = null ∘ filter (_==ᶜ_ c)

  syntax notElem c cs = c `notElem` cs

  elem : Char → List Char → Bool
  elem c = not ∘ notElem c

  syntax elem c cs = c `elem` cs

oneOf : List Char → Parser⊥ Char
oneOf cs = sat (λ c → c `elem` cs)

noneOf : List Char → Parser⊥ Char
noneOf cs = sat (λ c → c `notElem` cs)

{-
module ParserPgm where
  data ParserP : Set → Set₁ where
    `pure : ∀ {A} (x : A) → ParserP A
    `empty : ∀ {A} → ParserP A
    _`⟨|⟩_ : ∀ {A} → (p₁ p₂ : ParserP A) → ParserP A
    _`⊛_ : ∀ {A B} (p₁ : ParserP (A → B)) (p₂ : ParserP A) → ParserP B
    _`⊛♯_ : ∀ {A B} (p₁ : ParserP (A → B)) (p₂♯ : ∞(ParserP A)) → ParserP B
    -- _`>>=_ : ∀ {A B} (p₁ : ParserP A) → (f : A → ParserP B) → ParserP B
    `sat : (pred : Char → Bool) → ParserP Char
    -- `♯ : ∀ {A} (p♯ : ∞(ParserP A)) → ParserP A

  data ParserW : Set → Set₁ where
    `pure : ∀ {A} (x : A) → ParserW A
    `empty : ∀ {A} → ParserW A
    _`⟨|⟩_ : ∀ {A} → (p₁ p₂ : ParserW A) → ParserW A
    _`⊛_ : ∀ {A B} (p₁ : ParserW (A → B)) (p₂ : ParserP A) → ParserW B
    `sat : (pred : Char → Bool) → ParserW Char
    -- `♯ : ∀ {A} (p : ParserP A) → ParserW A

  whnf : ∀ {A} → ParserP A → ParserW A
  whnf (`pure x)   = `pure x
  whnf `empty      = `empty
  whnf (p₁ `⟨|⟩ p₂) = whnf p₁ `⟨|⟩ whnf p₂
  whnf (p₁ `⊛ p₂)  = whnf p₁ `⊛ p₂
  whnf (p₁ `⊛♯ p₂)  = whnf p₁ `⊛ (♭ p₂)
  whnf (`sat pred) = `sat pred
  -- whnf (`♯ p)      = `♯ (♭ p)


  mutual
    ⟦_⟧W : ∀ {A} → ParserW A → Parser⊥ A
    ⟦ `pure x   ⟧W = pure x
    ⟦ `empty    ⟧W = empty
    ⟦ p₁ `⟨|⟩ p₂ ⟧W = ⟦ p₁ ⟧W ⟨|⟩ ⟦ p₂ ⟧W
    ⟦ p₁ `⊛ p₂  ⟧W = ⟦ p₁ ⟧W ⊛ ⟦ p₂ ⟧P
    ⟦ `sat pred ⟧W = sat pred
    -- ⟦ `♯ p      ⟧W = ⟦ p ⟧P

    ⟦_⟧P : ∀ {A} → ParserP A → Parser⊥ A
    ⟦ p ⟧P = ⟦ whnf p ⟧W

{-
  runParserP : ∀ {A} → ParserP A → (Parser⊥ A)⊥
  runParserP (`pure x) = now $ pure x
  runParserP `empty = now $ empty
  runParserP (p₁ `⟨|⟩ p₂) = now _⟨|⟩_ ⊛⊥ runParserP p₁ ⊛⊥ runParserP p₂
  runParserP (p₁ `⊛ p₂) = now _⊛_ ⊛⊥ runParserP p₁ ⊛⊥ runParserP p₂
  runParserP (p₁ `⊛♯ p₂) = now _⊛_ ⊛⊥ runParserP p₁ ⊛⊥ runParserP p₂
  runParserP (`sat pred) = now $ sat pred
  -- runParserP (`♯ p♯) = later (♯ runParserP (♭ p♯))
-}
-}
