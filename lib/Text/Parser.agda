{-# OPTIONS --without-K #-}
open import Type using (★; ★_)
open import Data.Maybe.NP using (_→?_; module M?; just; maybe′; nothing; map?)
open import Data.Nat using (zero; suc)
open import Data.One using (𝟙)
open import Data.Char.NP renaming (_==_ to _==ᶜ_)
open import Data.List as L using (List; []; _∷_; null; filter)
open import Data.Vec using (Vec; []; _∷_)
open import Data.BoundedVec using (BoundedVec) renaming ([] to []ᵇᵛ; _∷_ to _∷ᵇᵛ_)
open import Data.Product.NP hiding (map)
open import Data.Bool using (Bool; if_then_else_; false)
open import Data.String using (String) renaming (toList to S▹L; fromList to L▹S)
open import Function.NP
open import Level.NP

module Text.Parser where

open M? ₀ using () renaming (_=<<_ to _=<<?_; _⊛_ to _⊛?_; join to join?)

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

eof : Parser 𝟙
eof s = if null s then pure _ [] else empty []

-- The remaning input is dropped, you may want to first
-- combine your parser `p' with `eof': `p <* eof'
runParser : ∀ {A} → Parser A → List Char →? A
runParser p s = map? fst (p s)

runParserˢ : ∀ {A} → Parser A → String →? A
runParserˢ p = runParser p ∘ S▹L

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

mapM : ∀ {a} {A : ★_ a} {B} → (A → Parser B) → List A → Parser (List B)
mapM f []       = pure []
mapM f (x ∷ xs) = ⟪ _∷_ · f x · mapM f xs ⟫

mapMvoid : ∀ {a} {A : ★_ a} {B} → (A → Parser B) → List A → Parser 𝟙
mapMvoid f []       = pure _
mapMvoid f (x ∷ xs) = f x *> mapMvoid f xs

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
manyBV (suc n) p = someBV n p ⟨|⟩ pure []ᵇᵛ

someBV n p = ⟪ _∷ᵇᵛ_ · p · manyBV n p ⟫

many : ∀ {A} n → Parser A → Parser (List A)
some : ∀ {A} n → Parser A → Parser (List A)

many 0       _ = empty
many (suc n) p = some n p ⟨|⟩ pure []

some n p = ⟪ _∷_ · p · many n p ⟫

manySat : (Char → Bool) → Parser (List Char)
manySat p []       = pure [] []
manySat p (x ∷ xs) = if p x then map? (first (_∷_ x)) (manySat p xs) else pure [] (x ∷ xs)

manySatˢ : (Char → Bool) → Parser String
manySatˢ = map L▹S ∘ manySat

someSat : (Char → Bool) → Parser (List Char)
someSat p = pure _∷_ ⊛ sat p ⊛ manySat p

someSatˢ : (Char → Bool) → Parser String
someSatˢ = map L▹S ∘ someSat

char : Char → Parser 𝟙
char c = sat (_==ᶜ_ c) *> pure _

string : String → Parser 𝟙
string = mapMvoid char ∘ S▹L

oneOf : List Char → Parser Char
oneOf cs = sat (λ c → c `elem` cs)

oneOfˢ : String → Parser Char
oneOfˢ = oneOf ∘ S▹L

noneOf : List Char → Parser Char
noneOf cs = sat (λ c → c `notElem` cs)

noneOfˢ : String → Parser Char
noneOfˢ = noneOf ∘ S▹L

someOneOf : List Char → Parser (List Char)
someOneOf cs = someSat (λ c → c `elem` cs)

someOneOfˢ : String → Parser String
someOneOfˢ = map L▹S ∘ someOneOf ∘ S▹L

someNoneOf : List Char → Parser (List Char)
someNoneOf cs = someSat (λ c → c `notElem` cs)

someNoneOfˢ : String → Parser String
someNoneOfˢ = map L▹S ∘ someNoneOf ∘ S▹L

manyOneOf : List Char → Parser (List Char)
manyOneOf cs = manySat (λ c → c `elem` cs)

manyOneOfˢ : String → Parser String
manyOneOfˢ = map L▹S ∘ manyOneOf ∘ S▹L

manyNoneOf : List Char → Parser (List Char)
manyNoneOf cs = manySat (λ c → c `notElem` cs)

manyNoneOfˢ : String → Parser String
manyNoneOfˢ = map L▹S ∘ manyNoneOf ∘ S▹L

lookSat : (List Char → Bool) → Parser 𝟙
lookSat p xs = if p xs then just (_ , xs) else nothing

lookSatHead : (Char → Bool) → Parser 𝟙
lookSatHead pᶜ = lookSat p
    where p : List Char → Bool
          p (x ∷ xs) = pᶜ x
          p []       = false

lookHeadNoneOf : List Char → Parser 𝟙
lookHeadNoneOf cs = lookSatHead (λ c → c `notElem` cs)

lookHeadNoneOfˢ : String → Parser 𝟙
lookHeadNoneOfˢ = lookHeadNoneOf ∘ S▹L

lookHeadSomeOf : List Char → Parser 𝟙
lookHeadSomeOf cs = lookSatHead (λ c → c `elem` cs)

lookHeadSomeOfˢ : String → Parser 𝟙
lookHeadSomeOfˢ = lookHeadSomeOf ∘ S▹L

module _ {A} where
    between : ∀ {_V} (begin end : Parser _V) → Endo (Parser A)
    between begin end p = begin *> p <* end

    betweenᶜ : (begin end : Char) → Endo (Parser A)
    betweenᶜ begin end = between (char begin) (char end)

    betweenˢ : (begin end : String) → Endo (Parser A)
    betweenˢ begin end = between (string begin) (string end)

    parens   = betweenᶜ '(' ')'
    braces   = betweenᶜ '{' '}'
    brackets = betweenᶜ '[' ']'
    angles   = betweenᶜ '<' '>'
    oxford   = betweenᶜ '⟦' '⟧'
