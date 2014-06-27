{-# OPTIONS --without-K #-}
module Reflection.NP where

open import Type
open import Level.NP
open import Data.Nat using (ℕ; zero; suc) renaming (_⊔_ to _⊔ℕ_)
open import Data.Maybe.NP
open import Data.Zero using (𝟘)
open import Data.One using (𝟙; 0₁)
open import Data.Two using (𝟚; 0₂; 1₂; [0:_1:_])
open import Data.List
open import Data.Vec using (Vec) -- ; []; _∷_)
open import Data.Product.NP
open import Function.NP hiding (Π)

open import Reflection public

Args : ★
Args = List (Arg Term)

-- lamᵛ : Term → Term
pattern lamᵛ = lam visible

-- lamʰ : Term → Term
pattern lamʰ = lam hidden

-- argiᵛʳ : Arg-info
pattern argiᵛʳ = arg-info visible relevant

-- argiʰʳ : Arg-info
pattern argiʰʳ = arg-info hidden relevant

-- argᵛʳ : ∀{A} → A → Arg A
pattern argᵛʳ v = arg argiᵛʳ v

-- argʰʳ : ∀{A} → A → Arg A
pattern argʰʳ v = arg argiʰʳ v

Arg-infos : ★
Arg-infos = List Arg-info

app` : (Args → Term) → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
app` f = go [] where
  go : Args → (ais : Arg-infos) → Term →⟨ length ais ⟩ Term
  go args []         = f (reverse args)
  go args (ai ∷ ais) = λ t → go (arg ai t ∷ args) ais

pattern conᵛʳ n t = con n (argᵛʳ t ∷ [])
pattern conʰʳ n t = con n (argʰʳ t ∷ [])
pattern defᵛʳ n t = def n (argᵛʳ t ∷ [])
pattern defʰʳ n t = def n (argʰʳ t ∷ [])

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

-- `★₀ : Term
pattern `★₀ = sort sort₀

-- el₀ : Term → Type
pattern el₀ t = el sort₀ t

-- Builds a type variable (of type ★₀)
``var₀ : ℕ → Args → Type
``var₀ n args = el₀ (var n args)

-- ``★₀ : Type
pattern ``★₀ = el sort₁ `★₀

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

-- sucSort : Sort → Sort
pattern sucSort s = set (`ₛ (sort s))

pattern `set₀ = set `₀
pattern `setₛ_ s = set (`ₛ s)
pattern `set_ s = set (sort s)

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

pattern piᵛʳ t u = pi (argᵛʳ t) u
pattern piʰʳ t u = pi (argʰʳ t) u

Π : Arg Type → Type → Type
Π t u = el (getSort (unArg t) `⊔` getSort u) (pi t u)

Πᵛʳ : Type → Type → Type
Πᵛʳ t u = el (getSort t `⊔` getSort u) (piᵛʳ t u)

Πʰʳ : Type → Type → Type
Πʰʳ t u = el (getSort t `⊔` getSort u) (piʰʳ t u)

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

-- fail
arityOfTerm unknown = []

-- absurd cases
arityOfTerm (lam _ _) = []

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
decode-ℕ `zero    = just 0
decode-ℕ (`suc t) = map? suc (decode-ℕ t)
decode-ℕ _        = nothing

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
  test₇ : decode-ℕ (quoteTerm (suc (suc zero))) ≡ just 2
  test₇ = refl
  test₈ : decode-ℕ (quoteTerm (suc (suc 3))) ≡ just 5
  test₈ = refl
  test₉ : decode-Maybe decode-𝟚 (quoteTerm (Maybe.just 0₂)) ≡ just (just 0₂)
  test₉ = refl
  test₁₀ : decode-List decode-ℕ (quoteTerm (0 ∷ 1 ∷ 2 ∷ [])) ≡ just (0 ∷ 1 ∷ 2 ∷ [])
  test₁₀ = refl
  test₁₁ : quoteTerm (_,′_ 0₂ 1₂) ≡ `0₂ `, `1₂
  test₁₁ = refl
  test₁₁' : decode-List (decode-Σ {A = 𝟚} {B = [0: 𝟚 1: ℕ ]} decode-𝟚 [0: decode-𝟚 1: decode-ℕ ])
                        (quoteTerm ((_,_ {B = [0: 𝟚 1: ℕ ]} 0₂ 1₂) ∷ (1₂ , 4) ∷ [])) ≡ just ((0₂ , 1₂) ∷ (1₂ , 4) ∷ [])
  test₁₁' = refl

-- -}
-- -}
-- -}
-- -}
