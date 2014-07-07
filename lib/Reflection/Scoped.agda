open import Reflection.NP using (Name; Arg; arg; Arg-info; arg-info; Literal; Visibility; visible; hidden; Relevance; relevant; irrelevant; Pattern; argᵛʳ; argʰʳ)
open import Level.NP
open import Data.List
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum.NP hiding (map)
open import Data.One
open import Data.Maybe.NP
open import Opaque

module Reflection.Scoped where
 
Scope : Set → (Set → Set) → Set → Set
Scope B F A = F (A ⊎ B)

mutual
  data Term (A : Set) : Set where
    -- Variable applied to arguments.
    var     : (x : A) (args : List (Arg (Term A))) → Term A
    -- Constructor applied to arguments.
    con     : (c : Name) (args : List (Arg (Term A))) → Term A
    -- Identifier applied to arguments.
    def     : (f : Name) (args : List (Arg (Term A))) → Term A
    -- Different kinds of λ-abstraction.
    lam     : (v : Visibility) (t : Scope 𝟙 Term A) → Term A
    -- Pattern matching λ-abstraction
    -- pat-lam : (cs : List (Clause A)) (args : List (Arg (Term A))) → Term A
    -- Pi-type.
    pi      : (t₁ : Arg (Type A)) (t₂ : Scope 𝟙 Type A) → Term A
    -- A sort.
    sort    : Sort A → Term A
    -- A literal.
    lit     : Literal → Term A
    -- Anything else.
    unknown : Term A

  data Type (A : Set) : Set where
    el : (s : Sort A) (t : Term A) → Type A

  data Sort (A : Set) : Set where
    -- A Set of a given (possibly neutral) level.
    set     : (t : Term A) → Sort A
    -- A Set of a given concrete level.
    lit     : (n : ℕ) → Sort A
    -- Anything else.
    unknown : Sort A

    {-
  data Clause (A : Set) : Set where
    clause : (ps : List (Arg Pattern)) → Scope (BoundPats ps) Term A → Clause A
    absurd-clause : List (Arg Pattern) → Clause A
    -}

Args : Set → Set
Args A = List (Arg (Term A))

unEl : ∀ {A} → Type A → Term A
unEl (el _ tm) = tm

getSort : ∀ {A} → Type A → Sort A
getSort (el s _) = s

unArg : ∀ {A} → Arg A → A
unArg (arg _ a) = a

-- sort₀ : Sort
pattern sort₀ = lit 0

-- sort₁ : Sort
pattern sort₁ = lit 1

-- `★_ : ℕ → Term
pattern  `★_ i = sort (lit i)

-- `★₀ : Term
pattern `★₀ = `★_ 0

-- el₀ : Term → Type
pattern el₀ t = el sort₀ t

-- Builds a type variable (of type ★₀)
{-
``var₀ : ℕ → Args → Type
``var₀ n args = el₀ (var n args)
-}

-- ``set : ℕ → ℕ → Type
pattern ``set i j = el (lit (suc j)) (`★_ i)

``★_ : ∀ {A} → ℕ → Type A
``★_ i = el (lit (suc i)) (`★_ i)

-- ``★₀ : Type
pattern ``★₀ = ``set 0 0

decode-Sort : ∀ {A} → Sort A → Maybe ℕ
--decode-Sort `set₀ = just zero
--decode-Sort (`setₛ_ s) = map? suc (decode-Sort (set s))
--decode-Sort (`set_ s) = decode-Sort s
decode-Sort (set _) = nothing
decode-Sort (lit n) = just n
decode-Sort unknown = nothing

pattern _`⊔_ s₁ s₂ = set (def (quote _⊔_) (argᵛʳ (sort s₁) ∷ argᵛʳ (sort s₂) ∷ []))

{-
_`⊔`_ : ∀ {A} → Sort A → Sort A → Sort A
s₁ `⊔` s₂ with decode-Sort s₁ | decode-Sort s₂
...          | just n₁        | just n₂        = lit (n₁ ⊔ℕ n₂)
...          | _              | _              = s₁ `⊔ s₂
-}

_`⊔`_ : ∀ {A} → Sort A → Scope 𝟙 Sort A → Sort A
s₁ `⊔` s₂ with decode-Sort s₁ | decode-Sort s₂
...          | just n₁        | just n₂        = lit (n₁ ⊔ℕ n₂)
...          | _              | _              = s₁ -- `⊔ s₂

pattern piᵛʳ t u = pi (argᵛʳ t) u
pattern piʰʳ t u = pi (argʰʳ t) u

`Π : ∀ {A} → Arg (Type A) → Scope 𝟙 Type A → Type A
`Π t u = el (getSort (unArg t) `⊔` getSort u) (pi t u)

`Πᵛʳ : ∀ {A} → Type A → Scope 𝟙 Type A → Type A
`Πᵛʳ t u = el (getSort t `⊔` getSort u) (piᵛʳ t u)

`Πʰʳ : ∀ {A} → Type A → Scope 𝟙 Type A → Type A
`Πʰʳ t u = el (getSort t `⊔` getSort u) (piʰʳ t u)

app : ∀ {A} → Term A → Args A → Term A
app (var x args) args₁ = var x (args ++ args₁)
app (con c args) args₁ = con c (args ++ args₁)
app (def f args) args₁ = def f (args ++ args₁)
app (lam v t) args = opaque "app/lam" unknown
-- app (pat-lam cs args) args₁ = opaque "app/pat-lam" unknown
app (pi t₁ t₂) args = opaque "app/pi" unknown
app (sort x) args = opaque "app/sort" unknown
app (lit x) args = opaque "app/lit" unknown
app unknown args = unknown

module Map where
    TermMap : (Set → Set) → Set₁
    TermMap F = ∀ {A B} → (A → B) → F A → F B

    ↑ : ∀ {A B C : Set} → (A → B) → (A ⊎ C) → (B ⊎ C)
    ↑ Γ (inl x) = inl (Γ x)
    ↑ Γ (inr y) = inr y

    term : TermMap Term
    tÿpe : TermMap Type
    args : TermMap Args
    sørt : TermMap Sort

    term Γ (var x as) = var (Γ x) (args Γ as)
    term Γ (con c as) = con c (args Γ as)
    term Γ (def d as) = def d (args Γ as)
    term Γ (lam v t) = lam v (term (↑ Γ) t)
    term Γ (pi (arg i t₁) t₂) = pi (arg i (tÿpe Γ t₁)) (tÿpe (↑ Γ) t₂)
    term Γ (sort x) = sort (sørt Γ x)
    term Γ (lit x) = lit x
    term Γ unknown = unknown

    tÿpe Γ (el s t) = el (sørt Γ s) (term Γ t)

    sørt Γ (set t) = set (term Γ t)
    sørt Γ (lit n) = lit n
    sørt Γ unknown = unknown

    args Γ []             = []
    args Γ (arg i t ∷ as) = arg i (term Γ t) ∷ args Γ as

-- Non-hereditary!
module Subst where
    VarSubst : Set → Set → Set
    VarSubst A B = A → Args B → Term B

    TermSubst : (Set → Set) → Set₁
    TermSubst F = ∀ {A B} → VarSubst A B → F A → F B

    ↑ : ∀ {A B C} → VarSubst A B → VarSubst (A ⊎ C) (B ⊎ C)
    ↑ Γ (inl x) as = app (Map.term inl (Γ x [])) as
    ↑ Γ (inr y) as = var (inr y) as

    term : TermSubst Term
    tÿpe : TermSubst Type
    args : TermSubst Args
    sørt : TermSubst Sort

    term Γ (var x as) = Γ x (args Γ as)
    term Γ (con c as) = con c (args Γ as)
    term Γ (def d as) = def d (args Γ as)
    term Γ (lam v t) = lam v (term (↑ Γ) t)
    term Γ (pi (arg i t₁) t₂) = pi (arg i (tÿpe Γ t₁)) (tÿpe (↑ Γ) t₂)
    term Γ (sort x) = sort (sørt Γ x)
    term Γ (lit x) = lit x
    term Γ unknown = unknown

    tÿpe Γ (el s t) = el (sørt Γ s) (term Γ t)

    sørt Γ (set t) = set (term Γ t)
    sørt Γ (lit n) = lit n
    sørt Γ unknown = unknown

    args Γ []             = []
    args Γ (arg i t ∷ as) = arg i (term Γ t) ∷ args Γ as
