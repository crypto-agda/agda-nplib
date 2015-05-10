{-# OPTIONS --without-K #-}
-- Inspired from https://www.fpcomplete.com/user/edwardk/heap-of-successes
--               https://gist.github.com/ekmett/578eaf3e5a37f7315e6c
--
-- Too slow so far: see an example in github.com/crypto-agda/crypto-agda Solver.Linear.Parser
open import Type using (Type; Type_)
open import Data.Maybe.NP using (_→?_; map?)
open import Data.Nat.NP using (ℕ; zero; suc; _<=_; _∸_; _+_) renaming (_==_ to _==ℕ_)
open import Data.One using (𝟙)
open import Data.Char.NP renaming (_==_ to _==ᶜ_)
open import Data.List.NP as L using (List; []; _∷_; null; filter)
open import Data.Vec using (Vec; []; _∷_)
open import Data.BoundedVec using (BoundedVec) renaming ([] to []ᵇᵛ; _∷_ to _∷ᵇᵛ_)
open import Data.Product.NP renaming (map to ×-map)
open import Data.Bool using (Bool; if_then_else_; false)
open import Data.String using (String) renaming (toList to S▹L; fromList to L▹S)
open import Function.NP
open import Level.NP

module Text.Parser.Heap where

-- Loosely typed assoc list with sorted keys
Heap : Type → Type
Heap A = List (ℕ × A)

module Heap {A : Type} where
  gather : Heap A → Heap (List A)
  gather [] = []
  gather ((i₀ , a₀) ∷ as₀) = go i₀ (a₀ ∷ []) as₀ where
    go : ℕ → _ → List _ → _
    go i acc [] = (i , acc) ∷ []
    go i acc ((j , a) ∷ as)
      = if i ==ℕ j then go i (a ∷ acc) as
                   else (i , acc) ∷ go j (a ∷ []) as

  -- fair interleaving, because, well, why not?
  merge : Heap A → Heap A → Heap A
  merge [] as = as
  merge as [] = as
  merge (a ∷ as) (b ∷ bs) =
    if fst a <= fst b then a ∷ merge (b ∷ bs) as
                      else b ∷ merge bs (a ∷ as)

  sing : ℕ → A → Heap A
  sing n a = (n , a) ∷ []

  map : ∀ {B} → (ℕ → ℕ) → (A → B) → Heap A → Heap B
  map f g = L.map (×-map f g)

  reset : Heap A → Heap A
  reset = L.map (first (const 0))
 
Parser : (I O : Type) → Type
Parser I O = I → Heap O

ParserL : (I O : Type) → Type
ParserL I O = Parser (List I) O

ParserLC = ParserL Char

module _ {I O : Type} where
  pure : O → Parser I O
  pure o i = Heap.sing 0 o

  empty : Parser I O
  empty _ = []

  infixr 3 _⟨|⟩_
  _⟨|⟩_ : (f g : Parser I O) → Parser I O
  (f ⟨|⟩ g) i = Heap.merge (f i) (g i)

  choices : List (Parser I O) → Parser I O
  choices = L.foldr _⟨|⟩_ empty

-- Parser is a Profunctor
dimap : ∀{I I' O O'}(f : I' → I)(g : O → O') → Parser I O → Parser I' O'
dimap f g p s = L.map (second g) (p (f s))

-- The remaning input is dropped, you may want to first
-- combine your parser `p' with `eof': `p <* eof'
runParser : ∀ {A} → ParserLC A → List Char →? A
runParser p = map? snd ∘ L.listToMaybe ∘ p

runParserˢ : ∀ {A} → ParserLC A → String →? A
runParserˢ p = runParser p ∘ S▹L

lookSat : ∀ {I} → (I → Bool) → Parser I 𝟙
lookSat p i = if p i then (0 , _) ∷ [] else []

notFollowedBy : ∀ {I O} → Parser I O → Parser I 𝟙
notFollowedBy m = lookSat (null ∘ m)

lookAhead : ∀ {I O} → Parser I O → Parser I O
lookAhead p = Heap.reset ∘ p

module _ {I : Type} where
  private
    M = ParserL I

  sat : (I → Bool) → M I
  sat pred (x ∷ xs) = if pred x then (1 , x) ∷ [] else []
  sat _    []       = []

  eof : M 𝟙
  eof = lookSat null

  infixr 0 _>>=_
  _>>=_ : ∀ {A B} → ParserL I A → (A → ParserL I B) → ParserL I B
  (ma >>= amb) s₀ = go 0 s₀ (ma s₀) [] where
    go : _ → _ → List _ → _ → _
    go i s ((j , a) ∷ fss) acc =
      let s' = L.drop (j ∸ i) s in
      go j s' fss (Heap.merge acc (L.map (first (_+_ j)) (amb a s')))
    go _ _ [] acc = acc

  infixl 0 _=<<_
  _=<<_ : ∀ {A B} → (A → ParserL I B) → ParserL I A → ParserL I B
  _=<<_ f pa = pa >>= f

  infixl 4 _⊛_ _*>_ _<*_
  _⊛_ : ∀ {A B} → ParserL I (A → B) → ParserL I A → ParserL I B
  (mf ⊛ ma) s₀ = go 0 s₀ (Heap.gather (mf s₀)) [] where
    go : _ → _ → List _ → _ → _
    go i s ((j , fs) ∷ fss) acc with L.drop (j ∸ i) s
    ... | s' =
      go j s' fss (Heap.merge acc (L.concatMap (λ { (k , a) → L.map (λ f -> (j + k , f a)) fs }) (ma s')))
    go _ _ [] acc = acc

  map : ∀ {A B} → (A → B) → ParserL I A → ParserL I B
  map f pa s₀ = Heap.map id f (pa s₀)

  {-
  map-spec : ∀ {A B}{f : A → B}{pa : ParserL I A} →
             map f pa ≡ pure f ⊛ pa
  map-spec rewrite ... concatMap-map = refl
  -}

  ⟪_·_⟫ : ∀ {A B} → (A → B) → M A → M B
  ⟪ f · x ⟫ = map f x

  ⟪_·_·_⟫ : ∀ {A B C} →
              (A → B → C) → M A → M B → M C
  ⟪ f · x · y ⟫ = map f x ⊛ y

  ⟪_·_·_·_⟫ : ∀ {A B C D} → (A → B → C → D)
              → M A → M B → M C → M D
  ⟪ f · x · y · z ⟫ = map f x ⊛ y ⊛ z

  _*>_ : ∀ {A B} → M A → M B → M B
  p₁ *> p₂ = ⟪ const id · p₁ · p₂ ⟫

  _<*_ : ∀ {A B} → M A → M B → M A
  p₁ <* p₂ = ⟪ const · p₁ · p₂ ⟫

  mapM : ∀ {a} {A : Type_ a} {B} → (A → M B) → List A → M (List B)
  mapM f []       = pure []
  mapM f (x ∷ xs) = ⟪ _∷_ · f x · mapM f xs ⟫

  mapMvoid : ∀ {a} {A : Type_ a} {B} → (A → M B) → List A → M 𝟙
  mapMvoid f []       = pure _
  mapMvoid f (x ∷ xs) = f x *> mapMvoid f xs

  module _ {A : Type} where
    join : ParserL I (ParserL I A) → ParserL I A
    join = _=<<_ id

    vec : ∀ n → M A → M (Vec A n)
    vec zero    p = pure []
    vec (suc n) p = ⟪ _∷_ · p · vec n p ⟫

    -- These are producing bounded vectors mainly for termination
    -- reasons.
    manyBV : ∀ n → M A → M (BoundedVec A n)
    someBV : ∀ n → M A → M (BoundedVec A (suc n))

    manyBV 0       _ = empty
    manyBV (suc n) p = someBV n p ⟨|⟩ pure []ᵇᵛ

    someBV n p = ⟪ _∷ᵇᵛ_ · p · manyBV n p ⟫

    many : ∀ n → M A → M (List A)
    some : ∀ n → M A → M (List A)

    many 0       _ = empty
    many (suc n) p = some n p ⟨|⟩ pure []

    some n p = ⟪ _∷_ · p · many n p ⟫

manySat : (Char → Bool) → ParserLC (List Char)
manySat p []       = (0 , []) ∷ []
manySat p (x ∷ xs) = if p x then Heap.map suc (_∷_ x) (manySat p xs) else (0 , []) ∷ []

manySatˢ : (Char → Bool) → ParserLC String
manySatˢ = map L▹S ∘ manySat

someSat : (Char → Bool) → ParserLC (List Char)
someSat p = pure _∷_ ⊛ sat p ⊛ manySat p

someSatˢ : (Char → Bool) → ParserLC String
someSatˢ = map L▹S ∘ someSat

char : Char → ParserLC 𝟙
char c = sat (_==ᶜ_ c) *> pure _

string : String → ParserLC 𝟙
string = mapMvoid char ∘ S▹L

oneOf : List Char → ParserLC Char
oneOf cs = sat (λ c → c `elem` cs)

oneOfˢ : String → ParserLC Char
oneOfˢ = oneOf ∘ S▹L

noneOf : List Char → ParserLC Char
noneOf cs = sat (λ c → c `notElem` cs)

noneOfˢ : String → ParserLC Char
noneOfˢ = noneOf ∘ S▹L

someOneOf : List Char → ParserLC (List Char)
someOneOf cs = someSat (λ c → c `elem` cs)

someOneOfˢ : String → ParserLC String
someOneOfˢ = map L▹S ∘ someOneOf ∘ S▹L

someNoneOf : List Char → ParserLC (List Char)
someNoneOf cs = someSat (λ c → c `notElem` cs)

someNoneOfˢ : String → ParserLC String
someNoneOfˢ = map L▹S ∘ someNoneOf ∘ S▹L

manyOneOf : List Char → ParserLC (List Char)
manyOneOf cs = manySat (λ c → c `elem` cs)

manyOneOfˢ : String → ParserLC String
manyOneOfˢ = map L▹S ∘ manyOneOf ∘ S▹L

manyNoneOf : List Char → ParserLC (List Char)
manyNoneOf cs = manySat (λ c → c `notElem` cs)

manyNoneOfˢ : String → ParserLC String
manyNoneOfˢ = map L▹S ∘ manyNoneOf ∘ S▹L

lookSatHead : (Char → Bool) → ParserLC 𝟙
lookSatHead pᶜ = lookSat p
    where p : List Char → Bool
          p (x ∷ xs) = pᶜ x
          p []       = false

lookHeadNoneOf : List Char → ParserLC 𝟙
lookHeadNoneOf cs = lookSatHead (λ c → c `notElem` cs)

lookHeadNoneOfˢ : String → ParserLC 𝟙
lookHeadNoneOfˢ = lookHeadNoneOf ∘ S▹L

lookHeadSomeOf : List Char → ParserLC 𝟙
lookHeadSomeOf cs = lookSatHead (λ c → c `elem` cs)

lookHeadSomeOfˢ : String → ParserLC 𝟙
lookHeadSomeOfˢ = lookHeadSomeOf ∘ S▹L

module _ {A} where
    between : ∀ {_V} (begin end : ParserLC _V) → Endo (ParserLC A)
    between begin end p = begin *> p <* end

    betweenᶜ : (begin end : Char) → Endo (ParserLC A)
    betweenᶜ begin end = between (char begin) (char end)

    betweenˢ : (begin end : String) → Endo (ParserLC A)
    betweenˢ begin end = between (string begin) (string end)

    parens   = betweenᶜ '(' ')'
    braces   = betweenᶜ '{' '}'
    brackets = betweenᶜ '[' ']'
    angles   = betweenᶜ '<' '>'
    oxford   = betweenᶜ '⟦' '⟧'

-- -}
-- -}
-- -}
-- -}
