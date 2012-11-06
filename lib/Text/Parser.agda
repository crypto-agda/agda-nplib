open import Type
open import Data.Maybe.NP as Maybe
open import Data.Nat
open import Data.Unit
open import Data.Char renaming (_==_ to _==ᶜ_)
open import Data.String as String
open import Data.List as L using (List; []; _∷_; null; filter)
open import Data.Vec using (Vec; []; _∷_)
import Data.BoundedVec as BV
open BV using (BoundedVec)
open import Data.Product.NP hiding (map)
open import Data.Bool
open import Function
import Level as L
import Category.Monad as Cat
import Category.Monad.Partiality.NP as Pa

module Text.Parser where

open M? L.zero using () renaming (_=<<_ to _=<<?_; _⊛_ to _⊛?_; join to join?)

Parser : ★ → ★
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

⟪_·_⟫ : ∀ {A B} → (A → B) → Parser A → Parser B
⟪ f · x ⟫ = map f x

⟪_·_·_⟫ : ∀ {A B C} →
            (A → B → C) → Parser A → Parser B → Parser C
⟪ f · x · y ⟫ = map f x ⊛ y

⟪_·_·_·_⟫ : ∀ {A B C D} → (A → B → C → D)
            → Parser A → Parser B → Parser C → Parser D
⟪ f · x · y · z ⟫ = map f x ⊛ y ⊛ z

_*>_ : ∀ {A B} → Parser A → Parser B → Parser B
p₁ *> p₂ = p₁ >>= const p₂

_<*_ : ∀ {A B} → Parser A → Parser B → Parser A
p₁ <* p₂ = p₁ >>= λ x → p₂ *> pure x

choices : ∀ {A} → List (Parser A) → Parser A
choices = L.foldr _⟨|⟩_ empty

vec : ∀ {A} n → Parser A → Parser (Vec A n)
vec zero    p = pure []
vec (suc n) p = ⟪ _∷_ · p · vec n p ⟫

-- These are producing bounded vectors mainly for termination
-- reasons.
manyBV : ∀ {A} n → Parser A → Parser (BoundedVec A n)
someBV : ∀ {A} n → Parser A → Parser (BoundedVec A (suc n))

manyBV 0       _ = empty
manyBV (suc n) p = someBV n p ⟨|⟩ pure BV.[]

someBV n p = ⟪ BV._∷_ · p · manyBV n p ⟫

many : ∀ {A} n → Parser A → Parser (List A)
some : ∀ {A} n → Parser A → Parser (List A)

many 0       _ = empty
many (suc n) p = some n p ⟨|⟩ pure []

some n p = ⟪ _∷_ · p · many n p ⟫

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

lookSat : (List Char → Bool) → Parser ⊤
lookSat p xs = if p xs then just (_ , xs) else nothing

lookSatHead : (Char → Bool) → Parser ⊤
lookSatHead pᶜ = lookSat p
    where p : List Char → Bool
          p (x ∷ xs) = pᶜ x
          p []       = false

lookHeadNoneOf : List Char → Parser ⊤
lookHeadNoneOf cs = lookSatHead (λ c → c `notElem` cs)

lookHeadSomeOf : List Char → Parser ⊤
lookHeadSomeOf cs = lookSatHead (λ c → c `elem` cs)
