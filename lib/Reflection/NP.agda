{-# OPTIONS --without-K #-}
module Reflection.NP where

open import Type
import Level as L
open L using (Level; _⊔_)
open import Data.Nat using (ℕ; zero; suc) renaming (_⊔_ to _⊔ℕ_)
open import Data.Maybe as May
open import Data.List
open import Data.Bool
open import Data.Product
open import Reflection public
open import Function

Args : ★
Args = List (Arg Term)

private
  primitive
    primQNameEquality : Name → Name → Bool

_==_ : Name → Name → Bool
_==_ = primQNameEquality

private
  _→⟨_⟩_ : ∀ (A : ★) (n : ℕ) (B : ★) → ★
  A →⟨ zero  ⟩ B = B
  A →⟨ suc n ⟩ B = A → A →⟨ n ⟩ B

  when : ∀ {A : ★} → Bool → Maybe A → Maybe A
  when true  x = x
  when false _ = nothing

  mapMaybe : ∀ {A B : ★} → (A → B) → Maybe A → Maybe B
  mapMaybe f (just x) = just (f x)
  mapMaybe f nothing  = nothing

lamᵛ : Term → Term
lamᵛ = lam visible

lamʰ : Term → Term
lamʰ = lam hidden

argᵛʳ : ∀{A} → A → Arg A
argᵛʳ = arg visible relevant

argʰʳ : ∀{A} → A → Arg A
argʰʳ = arg hidden relevant

Flags : ★
Flags = List (Visibility × Relevance)

app` : (Args → Term) → (fs : Flags) → Term →⟨ length fs ⟩ Term
app` f = go [] where
  go : Args → (fs : Flags) → Term →⟨ length fs ⟩ Term
  go args []             = f (reverse args)
  go args ((h , r) ∷ hs) = λ t → go (arg h r t ∷ args) hs

con` : Name → (fs : Flags) → Term →⟨ length fs ⟩ Term
con` x = app` (con x)

def` : Name → (fs : Flags) → Term →⟨ length fs ⟩ Term
def` x = app` (def x)

var` : ℕ → (fs : Flags) → Term →⟨ length fs ⟩ Term
var` x = app` (var x)

coe : ∀ {A : ★} {z : A} n → (Term →⟨ length (replicate n z) ⟩ Term) → Term →⟨ n ⟩ Term
coe zero    t = t
coe (suc n) f = λ t → coe n (f t)

con`ⁿʳ : Name → (n : ℕ) → Term →⟨ n ⟩ Term
con`ⁿʳ x n = coe n (app` (con x) (replicate n (visible , relevant)))

def`ⁿʳ : Name → (n : ℕ) → Term →⟨ n ⟩ Term
def`ⁿʳ x n = coe n (app` (def x) (replicate n (visible , relevant)))

var`ⁿʳ : ℕ → (n : ℕ) → Term →⟨ n ⟩ Term
var`ⁿʳ x n = coe n (app` (var x) (replicate n (visible , relevant)))

sort₀ : Sort
sort₀ = lit 0

sort₁ : Sort
sort₁ = lit 1

`★₀ : Term
`★₀ = sort sort₀

el₀ : Term → Type
el₀ = el sort₀

-- Builds a type variable (of type ★₀)
``var₀ : ℕ → Args → Type
``var₀ n args = el₀ (var n args)

``★₀ : Type
``★₀ = el sort₁ `★₀

unEl : Type → Term
unEl (el _ tm) = tm

getSort : Type → Sort
getSort (el s _) = s

unArg : ∀ {A} → Arg A → A
unArg (arg _ _ a) = a

`Level : Term
`Level = def (quote Level) []

``Level : Type
``Level = el₀ `Level

`sucLevel : Term → Term
`sucLevel = def`ⁿʳ (quote L.suc) 1

sucSort : Sort → Sort
sucSort s = set (`sucLevel (sort s))

ℕ→Level : ℕ → Level
ℕ→Level zero    = L.zero
ℕ→Level (suc n) = L.suc (ℕ→Level n)

decodeSort : Sort → Maybe ℕ
decodeSort (set (con c [])) = when (quote L.zero == c) (just zero)
decodeSort (set (con c (arg visible relevant s ∷ [])))
    = when (quote L.suc == c) (mapMaybe suc (decodeSort (set s)))
decodeSort (set (sort s)) = decodeSort s
decodeSort (set _) = nothing
decodeSort (lit n) = just n
decodeSort unknown = nothing

_`⊔`_ : Sort → Sort → Sort
s₁ `⊔` s₂ with decodeSort s₁ | decodeSort s₂
...          | just n₁       | just n₂        = lit (n₁ ⊔ℕ n₂)
...          | _             | _              = set (def (quote _⊔_) (argᵛʳ (sort s₁) ∷ argᵛʳ (sort s₂) ∷ []))

Π : Arg Type → Type → Type
Π t u = el (getSort (unArg t) `⊔` getSort u) (pi t u)

Πᵛʳ : Type → Type → Type
Πᵛʳ t u = el (getSort t `⊔` getSort u) (pi (arg visible relevant t) u)

Πʰʳ : Type → Type → Type
Πʰʳ t u = el (getSort t `⊔` getSort u) (pi (arg hidden relevant t) u)

-- η vs mk: performs no shifting of the result of mk.
-- Safe values of mk are def and con for instance
η : List Visibility → (Args → Term) → Term
η vs₀ mk = go vs₀ where
  vars : List Visibility → Args
  vars []       = []
  vars (v ∷ vs) = arg v relevant (var (length vs) []) ∷ vars vs
  go : List Visibility → Term
  go []       = mk (vars vs₀)
  go (v ∷ vs) = lam v (go vs)

ηʰ : ℕ → (Args → Term) → Term
ηʰ n = η (replicate n hidden)

ηᵛ : ℕ → (Args → Term) → Term
ηᵛ n = η (replicate n visible)

ηʰⁿ : ℕ → Name → Term
ηʰⁿ n = ηʰ n ∘ def

ηᵛⁿ : ℕ → Name → Term
ηᵛⁿ n = ηᵛ n ∘ def

arityOfType : Type → List Visibility
arityOfType (el _ u) with u
... | pi (arg v _ _) t = v ∷ arityOfType t

-- no more arguments
... | var _ _ = []

-- TODO
... | con c args = []
... | def f args = []
... | sort s = []

-- fail
... | unknown = []

-- absurd cases
... | lam _ _ = []

ηⁿ : Name → Term
ηⁿ nm = η (arityOfType (type nm)) (def nm)

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
{-
  ηh₂ = ηⁿ (quote h₂)
  test₆ : unquote ηh₂ ≡ {!!} -- λ {x y : ℕ} {{z : ℕ}} (t u : ℕ) {v : ℕ} → h {x} {y} {{z}} t u {v}
  test₆ = refl

  here = {!!}
-}
