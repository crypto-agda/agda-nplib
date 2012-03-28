open import Data.Maybe.NP as Maybe
open import Data.Nat
open import Data.Unit
open import Data.Char renaming (_==_ to _==ᶜ_)
open import Data.String as String
open import Data.List as L using (List; []; _∷_; null; filter)
open import Data.Product.NP hiding (map)
open import Data.Bool
open import Function
import Level as L
import Category.Monad as Cat
import Category.Monad.Partiality.NP as Pa

module Text.Parser where

open M? L.zero using () renaming (_=<<_ to _=<<?_; _⊛_ to _⊛?_; join to join?)

Parser : Set → Set
Parser A = List Char →? (A × List Char)

pure : ∀ {A} → A → Parser A
pure a s = just (a , s)

infixr 3 _⟨|⟩_
_⟨|⟩_ : ∀ {A} → (f g : Parser A) → Parser A
_⟨|⟩_ f g s = maybe′ just (g s) $ f s

empty : ∀ {A} → Parser A
empty _ = nothing

sat : (Char → Bool) → Parser Char
sat pred (x ∷ xs) = (if pred x then pure x else empty) xs
sat _    []       = nothing

eof : Parser ⊤
eof s = if null s then pure _ [] else empty []

-- The remaning input is dropped, you may want to first
-- combine your parser `p' with `eof': `p <* eof'
runParser : ∀ {A} → Parser A → List Char →? A
runParser p s = map? proj₁ (p s)

infixr 0 _>>=_
_>>=_ : ∀ {A B} → Parser A → (A → Parser B) → Parser B
_>>=_ pa f = maybe′ (uncurry f) nothing ∘ pa

infixl 0 _=<<_
_=<<_ : ∀ {A B} → (A → Parser B) → Parser A → Parser B
_=<<_ f pa = pa >>= f

join : ∀ {A} → Parser (Parser A) → Parser A
join = _=<<_ id

map : ∀ {A B} → (A → B) → Parser A → Parser B
map f pa = pa >>= pure ∘ f

infixl 4 _⊛_ _*>_ _<*_
_⊛_ : ∀ {A B} → Parser (A → B) → Parser A → Parser B
_⊛_ pf pa = pf >>= λ f → pa >>= λ a → pure (f a)

_*>_ : ∀ {A B} → Parser A → Parser B → Parser B
p₁ *> p₂ = p₁ >>= const p₂

_<*_ : ∀ {A B} → Parser A → Parser B → Parser A
p₁ <* p₂ = p₁ >>= λ x → p₂ *> pure x

choices : ∀ {A} → List (Parser A) → Parser A
choices = L.foldr _⟨|⟩_ empty

{-
mutual
  many : ∀ {A} → Parser A → Parser (List A)
  many p = some p ⟨|⟩ pure []

  some : ∀ {A} → Parser A → Parser (List A)
  some p = pure _∷_ ⊛ p ⊛ many p
-}

mutual
  many : ∀ {A} → Parser A → ℕ → Parser (List A)
  many _ 0       = empty
  many p (suc n) = some p n ⟨|⟩ pure []

  some : ∀ {A} → Parser A → ℕ → Parser (List A)
  some p n = pure _∷_ ⊛ p ⊛ many p n

manySat : (Char → Bool) → Parser (List Char)
manySat p []       = pure [] []
manySat p (x ∷ xs) = if p x then map? (first (_∷_ x)) (manySat p xs) else pure [] (x ∷ xs)

someSat : (Char → Bool) → Parser (List Char)
someSat p = pure _∷_ ⊛ sat p ⊛ manySat p

char : Char → Parser ⊤
char c = sat (_==ᶜ_ c) *> pure _

private
  notElem : Char → List Char → Bool
  notElem c = null ∘ filter (_==ᶜ_ c)

  syntax notElem c cs = c `notElem` cs

  elem : Char → List Char → Bool
  elem c = not ∘ notElem c

  syntax elem c cs = c `elem` cs

oneOf : List Char → Parser Char
oneOf cs = sat (λ c → c `elem` cs)

noneOf : List Char → Parser Char
noneOf cs = sat (λ c → c `notElem` cs)

someOneOf : List Char → Parser (List Char)
someOneOf cs = someSat (λ c → c `elem` cs)

someNoneOf : List Char → Parser (List Char)
someNoneOf cs = someSat (λ c → c `notElem` cs)

manyOneOf : List Char → Parser (List Char)
manyOneOf cs = manySat (λ c → c `elem` cs)

manyNoneOf : List Char → Parser (List Char)
manyNoneOf cs = manySat (λ c → c `notElem` cs)
