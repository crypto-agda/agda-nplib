{-# OPTIONS --without-K #-}
module Reflection.NP where

open import Opaque
open import Type
open import Level.NP
open import Data.Nat using (ℕ; zero; suc; _+_) renaming (_⊔_ to _⊔ℕ_)
open import Data.Maybe.NP
open import Data.Zero using (𝟘)
open import Data.One using (𝟙; 0₁)
open import Data.Two using (𝟚; 0₂; 1₂; [0:_1:_])
open import Data.List
open import Data.Vec using (Vec) -- ; []; _∷_)
open import Data.Product.NP
open import Function.NP

open import Reflection public

Args : ★
Args = List (Arg Term)

-- lamᵛ : Term → Term
pattern lamᵛ = lam visible

-- lamʰ : Term → Term
pattern lamʰ = lam hidden

-- argiᵛ : Relevance → Arg-info
pattern argiᵛ x = arg-info visible x

-- argiʳ : Visibility → Arg-info
pattern argiʳ x = arg-info x relevant

-- argiᵛʳ : Arg-info
pattern argiᵛʳ = argiᵛ relevant

-- argiʰ : Relevance → Arg-info
pattern argiʰ x = arg-info hidden x

-- argiʰʳ : Arg-info
pattern argiʰʳ = argiʰ relevant

-- argᵛ : ∀{A} → Relevance → A → Arg A
pattern argᵛ r v = arg (argiᵛ r) v

-- argᵛʳ : ∀{A} → Visibility → A → Arg A
pattern argʳ v x = arg (argiʳ v) x

-- argʰ : ∀{A} → Relevance → A → Arg A
pattern argʰ r v = arg (argiʰ r) v

-- argᵛʳ : ∀{A} → A → Arg A
pattern argᵛʳ v = arg argiᵛʳ v

-- argʰʳ : ∀{A} → A → Arg A
pattern argʰʳ v = arg argiʰʳ v

pattern conᵛ n r t = con n (argᵛ r t ∷ [])
pattern conʰ n r t = con n (argʰ r t ∷ [])
pattern defᵛ n r t = def n (argᵛ r t ∷ [])
pattern defʰ n r t = def n (argʰ r t ∷ [])

pattern conᵛʳ n t = con n (argᵛʳ t ∷ [])
pattern conʰʳ n t = con n (argʰʳ t ∷ [])
pattern defᵛʳ n t = def n (argᵛʳ t ∷ [])
pattern defʰʳ n t = def n (argʰʳ t ∷ [])

Arg-infos : ★
Arg-infos = List Arg-info

app` : (Args → Term) → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
app` f = go [] where
  go : Args → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
  go args []         = f (reverse args)
  go args (ai ∷ ais) = λ t → go (arg ai t ∷ args) ais

con` : Name → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
con` x = app` (con x)

def` : Name → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
def` x = app` (def x)

var` : ℕ → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
var` x = app` (var x)

coe : ∀ {A : ★} {z : A} n → (Term →⟨ length (replicate n z) ⟩ Term) → Term →⟨ n ⟩ Term
coe zero    t = t
coe (suc n) f = λ t → coe n (f t)

con`ⁿʳ : Name → (n : ℕ) → Term →⟨ n ⟩ Term
con`ⁿʳ x n = coe n (app` (con x) (replicate n argiᵛʳ))

def`ⁿʳ : Name → (n : ℕ) → Term →⟨ n ⟩ Term
def`ⁿʳ x n = coe n (app` (def x) (replicate n argiᵛʳ))

var`ⁿʳ : ℕ → (n : ℕ) → Term →⟨ n ⟩ Term
var`ⁿʳ x n = coe n (app` (var x) (replicate n argiᵛʳ))

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
``var₀ : ℕ → Args → Type
``var₀ n args = el₀ (var n args)

-- ``set : ℕ → ℕ → Type
pattern ``set i j = el (lit (suc j)) (`★_ i)

``★_ : ℕ → Type
``★_ i = el (lit (suc i)) (`★_ i)

-- ``★₀ : Type
pattern ``★₀ = ``set 0 0

unEl : Type → Term
unEl (el _ tm) = tm

getSort : Type → Sort
getSort (el s _) = s

unArg : ∀ {A} → Arg A → A
unArg (arg _ a) = a

-- `Level : Term
pattern `Level = def (quote Level) []

-- ``Level : Type
pattern ``Level = el₀ `Level

pattern `₀ = def (quote ₀) []

-- `ₛ_ : Term → Term
-- `ₛ_ = def`ⁿʳ (quote L.suc) 1
pattern `ₛ_ v = def (quote ₛ) (argᵛʳ v ∷ [])

-- `suc-sort : Sort → Sort
pattern `suc-sort s = set (`ₛ (sort s))

pattern `set₀ = set `₀
pattern `setₛ_ s = set (`ₛ s)
pattern `set_ s = set (sort s)

suc-sort : Sort → Sort
suc-sort (set t) = set (`ₛ t)
suc-sort (lit n) = lit (suc n)
suc-sort unknown = unknown

decode-Sort : Sort → Maybe ℕ
decode-Sort `set₀ = just zero
decode-Sort (`setₛ_ s) = map? suc (decode-Sort (set s))
decode-Sort (`set_ s) = decode-Sort s
decode-Sort (set _) = nothing
decode-Sort (lit n) = just n
decode-Sort unknown = nothing

pattern _`⊔_ s₁ s₂ = set (def (quote _⊔_) (argᵛʳ (sort s₁) ∷ argᵛʳ (sort s₂) ∷ []))

_`⊔`_ : Sort → Sort → Sort
s₁ `⊔` s₂ with decode-Sort s₁ | decode-Sort s₂
...          | just n₁        | just n₂        = lit (n₁ ⊔ℕ n₂)
...          | _              | _              = s₁ `⊔ s₂

mapVar : (ℕ → ℕ) → Term → Term
mapVarArgs : (ℕ → ℕ) → Args → Args
mapVarType : (ℕ → ℕ) → Type → Type
mapVarSort : (ℕ → ℕ) → Sort → Sort

mapVar↑ : (ℕ → ℕ) → (ℕ → ℕ)
mapVar↑ f zero    = zero
mapVar↑ f (suc n) = suc (f n)

mapVar f (var x args) = var (f x) (mapVarArgs f args)
mapVar f (con c args) = con c (mapVarArgs f args)
mapVar f (def d args) = def d (mapVarArgs f args)
mapVar f (lam v t) = lam v (mapVar (mapVar↑ f) t)
mapVar f (pat-lam cs args) = unknown
mapVar f (pi (arg i t₁) t₂) = pi (arg i (mapVarType f t₁)) (mapVarType (mapVar↑ f) t₂)
mapVar f (sort x) = sort (mapVarSort f x)
mapVar f (lit x) = lit x
mapVar f unknown = unknown

mapVarArgs f [] = []
mapVarArgs f (arg i x ∷ as) = arg i (mapVar f x) ∷ mapVarArgs f as
mapVarType f (el s t) = el (mapVarSort f s) (mapVar f t)
mapVarSort f (set t) = set (mapVar f t)
mapVarSort f (lit n) = lit n
mapVarSort f unknown = unknown

liftTerm : Term → Term
liftTerm = mapVar suc

liftType : Type → Type
liftType = mapVarType suc

pattern piᵛʳ t u = pi (argᵛʳ t) u
pattern piʰʳ t u = pi (argʰʳ t) u

`Π : Arg Type → Type → Type
`Π t u = el (getSort (unArg t) `⊔` getSort u) (pi t u)

`Πᵛʳ : Type → Type → Type
`Πᵛʳ t u = el (getSort t `⊔` getSort u) (piᵛʳ t u)

`Πʰʳ : Type → Type → Type
`Πʰʳ t u = el (getSort t `⊔` getSort u) (piʰʳ t u)

_`→_ : Arg Type → Type → Type
t `→ u = `Π t (liftType u)

_`→ʰʳ_ : Type → Type → Type
t `→ʰʳ u = `Πʰʳ t (liftType u)

_`→ᵛʳ_ : Type → Type → Type
t `→ᵛʳ u = `Πᵛʳ t (liftType u)

-- η vs mk: performs no shifting of the result of mk.
-- Safe values of mk are def and con for instance
η : List Arg-info → (Args → Term) → Term
η ais₀ mk = go ais₀ where
  vars : List Arg-info → Args
  vars []         = []
  vars (ai ∷ ais) = arg ai (var (length ais) []) ∷ vars ais
  go : List Arg-info → Term
  go []                   = mk (vars ais₀)
  go (arg-info v _ ∷ ais) = lam v (go ais)

ηʰ : ℕ → (Args → Term) → Term
ηʰ n = η (replicate n argiʰʳ)

ηᵛ : ℕ → (Args → Term) → Term
ηᵛ n = η (replicate n argiᵛʳ)

ηʰⁿ : ℕ → Name → Term
ηʰⁿ n = ηʰ n ∘ def

ηᵛⁿ : ℕ → Name → Term
ηᵛⁿ n = ηᵛ n ∘ def

arityOfTerm : Term → List Arg-info
arityOfType : Type → List Arg-info

arityOfType (el _ u) = arityOfTerm u
arityOfTerm (pi (arg ai _) t) = ai ∷ arityOfType t

-- no more arguments
arityOfTerm (var _ _) = []

-- TODO
arityOfTerm (con c args) = []
arityOfTerm (def f args) = []
arityOfTerm (sort s)     = []
arityOfTerm (lit _)      = []

-- fail
arityOfTerm unknown = []

-- absurd cases
arityOfTerm (lam _ _) = []
arityOfTerm (pat-lam _ _) = []

ηⁿ : Name → Term
ηⁿ nm = η (arityOfType (type nm)) (def nm)

Decode-Term : ∀ {a} → ★_ a → ★_ a
Decode-Term A = Term → Maybe A

pattern `𝟘 = def (quote 𝟘) []

pattern `𝟙  = def (quote 𝟙) []
pattern `0₁ = con (quote 0₁) []

decode-𝟙 : Decode-Term 𝟙
decode-𝟙 `0₁ = just 0₁
decode-𝟙 _   = nothing

pattern `𝟚  = def (quote 𝟚) []
pattern `0₂ = con (quote 0₂) []
pattern `1₂ = con (quote 1₂) []

decode-𝟚 : Decode-Term 𝟚
decode-𝟚 `0₂ = just 0₂
decode-𝟚 `1₂ = just 1₂
decode-𝟚 _   = nothing

pattern `ℕ     = def (quote ℕ) []
pattern `zero  = con (quote zero) []
pattern `suc t = conᵛʳ (quote suc) t

decode-ℕ : Decode-Term ℕ
decode-ℕ (lit (nat n)) = just n
-- these two should not happen anymore:
decode-ℕ `zero         = just 0
decode-ℕ (`suc t)      = map? suc (decode-ℕ t)
decode-ℕ _             = nothing

pattern `Maybe t = defᵛʳ (quote Maybe) t
pattern `nothing = con (quote Maybe.nothing) []
pattern `just  t = conᵛʳ (quote Maybe.just) t

decode-Maybe : ∀ {a} {A : ★_ a} → Decode-Term A → Decode-Term (Maybe A)
decode-Maybe decode-A `nothing  = just nothing
decode-Maybe decode-A (`just t) = map? just (decode-A t)
decode-Maybe decode-A _         = nothing

pattern `List t = defᵛʳ (quote List) t
pattern `[] = con (quote List.[]) []
pattern _`∷_ t u = con (quote List._∷_) (argᵛʳ t ∷ argᵛʳ u ∷ [])

decode-List : ∀ {a} {A : ★_ a} → Decode-Term A → Decode-Term (List A)
decode-List decode-A `[]      = just []
decode-List decode-A (t `∷ u) = ⟪ _∷_ · decode-A t · decode-List decode-A u ⟫?
decode-List decode-A _        = nothing

pattern `Vec t u = def (quote Vec) (argᵛʳ t ∷ argᵛʳ u ∷ [])
pattern `v[]      = con (quote Vec.[]) []
pattern _`v∷_ t u = con (quote Vec._∷_) (argᵛʳ t ∷ argᵛʳ u ∷ [])

{-
decode-Vec : ∀ {a} {A : ★_ a} {n} → Decode-Term A → Decode-Term (Vec A n)
decode-Vec decode-A `[]      = just []
decode-Vec decode-A (t `∷ u) = ⟪ _∷_ · decode-A t · decode-Vec decode-A u ⟫?
decode-Vec decode-A _        = nothing
-}

pattern `Σ t u = def (quote Σ) (argᵛʳ t ∷ argᵛʳ u ∷ [])
pattern _`,_ t u = con (quote _,_) (argᵛʳ t ∷ argᵛʳ u ∷ [])
pattern `fst t = defᵛʳ (quote fst) t
pattern `snd t = defᵛʳ (quote snd) t

module _ {a b} {A : ★_ a} {B : A → ★_ b}
         (decode-A : Decode-Term A)
         (decode-B : (x : A) → Decode-Term (B x))
         where
    decode-Σ : Decode-Term (Σ A B)
    decode-Σ (t `, u) = decode-A t   >>=? λ x →
                        decode-B x u >>=? λ y →
                        just (x , y)
    decode-Σ _        = nothing

data Abs : Set where
  var : ℕ → Abs
  []  : Abs
  _,_ : Abs → Abs → Abs
  abs : Abs → Abs

_,,_ : Abs → Abs → Abs
[]      ,, x  = x
x       ,, [] = x
(x , y) ,, z  = x ,, (y ,, z)
x       ,, y  = x , y

abs' : Abs → Abs
abs' [] = []
abs' x  = abs x

absTerm : Term → Abs
absArgs : Args → Abs
absType : Type → Abs
absSort : Sort → Abs

absTerm (var x args) = var x ,, absArgs args
absTerm (con c args) = absArgs args
absTerm (def f args) = absArgs args
absTerm (lam v t) = abs' (absTerm t)
absTerm (pat-lam cs args) = opaque "absTm/pat-lam" []
absTerm (pi (arg _ t₁) t₂) = absType t₁ ,, abs' (absType t₂)
absTerm (sort x) = absSort x
absTerm (lit x) = []
absTerm unknown = []

absArgs [] = []
absArgs (arg i x ∷ as) = absTerm x ,, absArgs as
absType (el _ t) = absTerm t
absSort (set t) = absTerm t
absSort (lit n) = []
absSort unknown = []

app : Term → Args → Term
app (var x args) args₁ = var x (args ++ args₁)
app (con c args) args₁ = con c (args ++ args₁)
app (def f args) args₁ = def f (args ++ args₁)
app (lam v t) args = opaque "app/lam" unknown
app (pat-lam cs args) args₁ = opaque "app/pat-lam" unknown
app (pi t₁ t₂) args = opaque "app/pi" unknown
app (sort x) args = opaque "app/sort" unknown
app (lit x) args = opaque "app/lit" unknown
app unknown args = unknown

quoteNat : ℕ → Term
quoteNat zero    = `zero
quoteNat (suc n) = `suc (quoteNat n)

unlit : Literal → Term
unlit (nat x) = quoteNat x
unlit x = lit x

unknown-fun-def : FunctionDef
unknown-fun-def = opaque "unknown-fun-def" (fun-def (el unknown unknown) [])

unknown-definition : Definition
unknown-definition = opaque "unknown-definition" (function unknown-fun-def)

un-function : Definition → FunctionDef
un-function (function x) = x
un-function _            = unknown-fun-def

module Map-arg-info (f : Arg-info → Arg-info) where

    On : Set → Set
    On T = T → T

    pat : On Pattern
    pats : On (List (Arg Pattern))
    pat (con c ps) = con c (pats ps)
    pat dot = dot
    pat var = var
    pat (lit l) = lit l
    pat (proj p) = proj p
    pat absurd = absurd
    pats [] = []
    pats (arg i p ∷ ps) = arg (f i) (pat p) ∷ pats ps

    term : On Term
    tÿpe : On Type
    årgs : On Args
    sørt : On Sort
    clåuse  : On Clause
    clåuses : On (List Clause)

    term (var x as) = var x (årgs as)
    term (con c as) = con c (årgs as)
    term (def f as) = def f (årgs as)
    term (lam v t) = lam (visibility (f (arg-info v (relevant{- arbitrary choice -})))) (term t)
    term (pat-lam cs as) = pat-lam (clåuses cs) (årgs as)
    term (pi (arg i t₁) t₂) = pi (arg (f i) (tÿpe t₁)) (tÿpe t₂)
    term (sort s) = sort (sørt s)
    term (lit l) = lit l
    term unknown = unknown

    tÿpe (el s t) = el (sørt s) (term t)

    årgs [] = []
    årgs (arg i t ∷ as) = arg (f i) (term t) ∷ årgs as

    sørt (set t) = set (term t)
    sørt (lit n) = lit n
    sørt unknown = unknown

    clåuse (clause ps body) = clause (pats ps) (term body)
    clåuse (absurd-clause ps) = absurd-clause (pats ps)

    clåuses [] = []
    clåuses (x ∷ cs) = clåuse x ∷ clåuses cs

    fün-def : FunctionDef → FunctionDef
    fün-def (fun-def t cs) = fun-def (tÿpe t) (clåuses cs)

    dëf : Definition → Definition
    dëf (function x) = function (fün-def x)
    dëf (data-type x) = opaque "Map-arg-info.dëf/data-type" unknown-definition
    dëf (record′ x) = opaque "Map-arg-info.dëf/record′" unknown-definition
    dëf constructor′ = opaque "Map-arg-info.dëf/constructor′" unknown-definition
    dëf axiom = opaque "Map-arg-info.dëf/axiom" unknown-definition
    dëf primitive′ = opaque "Map-arg-info.dëf/primitive′" unknown-definition

    nåme : Name → Definition
    nåme = dëf ∘ definition

reveal-arg : Arg-info → Arg-info
reveal-arg (arg-info v r) = arg-info visible r

module Reveal-args = Map-arg-info reveal-arg

module Get-clauses where
    from-fun-def : FunctionDef → Clauses
    from-fun-def (fun-def _ cs) = cs
    from-def : Definition → Clauses
    from-def (function x) = from-fun-def x
    from-def (data-type x) = opaque "Get-clauses.from-def/data-type" []
    from-def (record′ x) = opaque "Get-clauses.from-def/record′" []
    from-def constructor′ = opaque "Get-clauses.from-def/constructor′" []
    from-def axiom = opaque "Get-clauses.from-def/axiom" []
    from-def primitive′ = opaque "Get-clauses.from-def/primitive′" []
    from-name : Name → Clauses
    from-name n = from-def (definition n)

module Get-type where
    from-clause : Clause → Term
    from-clause (clause [] body) = body
    from-clause (clause (arg _ var ∷ pats) body)
      = lam visible (from-clause (clause pats body))
    from-clause _ = unknown
    from-fun-def : FunctionDef → Type
    from-fun-def (fun-def t _) = t
    from-def : Definition → Type
    from-def (function x) = from-fun-def x
    from-def (data-type x) = opaque "Get-type.from-def/data-type" ``★₀
    from-def (record′ x) = opaque "Get-type.from-def/record′" ``★₀
    from-def constructor′ = opaque "Get-type.from-def/constructor" ``★₀
    from-def axiom = opaque "Get-type.from-def/axiom" ``★₀
    from-def primitive′ = opaque "Get-type.from-def/primitive′" ``★₀
    from-name : Name → Type
    from-name n = from-def (definition n)

module Get-term where
    from-clause : Clause → Term
    from-clause (clause [] body) = body
    from-clause (clause (arg _ var ∷ pats) body)
      = lam visible (from-clause (clause pats body))
    from-clause _ = unknown
    from-fun-def : FunctionDef → Term
    from-fun-def (fun-def _ (c ∷ [])) = from-clause c
    from-fun-def _ = unknown
    from-def : Definition → Term
    from-def (function x) = from-fun-def x
    from-def (data-type x) = unknown
    from-def (record′ x) = unknown
    from-def constructor′ = unknown
    from-def axiom = unknown
    from-def primitive′ = unknown
    from-name : Name → Term
    from-name n = from-def (definition n)

module Ex where
  open import Relation.Binary.PropositionalEquality
  postulate
    f : ℕ → ℕ → ℕ
    g : {x y : ℕ} → ℕ
    h : {x y : ℕ} {{z : ℕ}} (t u : ℕ) {v : ℕ} → ℕ
  H : ★
  H = {x y : ℕ} {{z : ℕ}} (t u : ℕ) {v : ℕ} → ℕ
  postulate
    h₂ : H
  test₁ : unquote (ηᵛⁿ 2 (quote f)) ≡ f
  test₁ = refl
  test₂ : unquote (ηʰⁿ 2 (quote g)) ≡ λ {x y : ℕ} → g {x} {y}
  test₂ = refl
  test₃ : unquote (ηⁿ (quote f)) ≡ f
  test₃ = refl
  test₄ : unquote (ηⁿ (quote g)) ≡ λ {x y : ℕ} → g {x} {y}
  test₄ = refl
  ηh = ηⁿ (quote h)
  -- this test passes but leave an undecided instance argument
  -- test₅ : unquote ηh ≡ λ {x y : ℕ} {{z : ℕ}} (t u : ℕ) {v : ℕ} → h {x} {y} {{z}} t u {v}
  -- test₅ = refl
  ηh₂ : Term
  ηh₂ = ηⁿ (quote h₂)
  {-
  test₆ : unquote ηh₂ ≡ {!unquote ηh₂!} -- λ {x y : ℕ} {{z : ℕ}} (t u : ℕ) {v : ℕ} → h {x} {y} {{z}} t u {v}
  test₆ = refl
  -}
  test₇ : decode-ℕ (quoteTerm (ℕ.suc (suc zero))) ≡ just 2
  test₇ = refl
  test₈ : decode-ℕ (quoteTerm (ℕ.suc (suc 3))) ≡ just 5
  test₈ = refl
  test₉ : decode-Maybe decode-𝟚 (quoteTerm (Maybe.just 0₂)) ≡ just (just 0₂)
  test₉ = refl
  test₁₀ : decode-List decode-ℕ (quoteTerm (0 ∷ 1 ∷ 2 ∷ [])) ≡ just (0 ∷ 1 ∷ 2 ∷ [])
  test₁₀ = refl
  test₁₁ : quoteTerm (_,′_ 0₂ 1₂) ≡ `0₂ `, `1₂
  test₁₁ = refl
  test₁₁' : decode-List (decode-Σ {A = 𝟚} {B = [0: 𝟚 1: ℕ ]} decode-𝟚 [0: decode-𝟚 1: decode-ℕ ])
                        (quoteTerm ((Σ._,_ {B = [0: 𝟚 1: ℕ ]} 0₂ 1₂) ∷ (1₂ , 4) ∷ [])) ≡ just ((0₂ , 1₂) ∷ (1₂ , 4) ∷ [])
  test₁₁' = refl

-- -}
-- -}
-- -}
-- -}
