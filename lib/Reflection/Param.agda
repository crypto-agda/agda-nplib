open import Function
open import Opaque
open import Type
open import Data.Zero
open import Data.One hiding (_≟_)
open import Data.Two hiding (_≟_)
open import Data.Two.Logical
open import Data.Nat hiding (_≟_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; []; _∷_; replicate; tabulate; allFin; reverse; _⊛_; toList) renaming (map to vmap)
open import Data.Nat.Logical hiding (_≟_) renaming (zero to ⟦zero⟧; suc to ⟦suc⟧)
open import Data.List hiding (replicate; reverse)
open import Data.Sum.NP
open import Reflection.NP
open import Relation.Unary.Logical
open import Relation.Binary.Logical
open import Relation.Nullary.NP
open import Relation.Binary.PropositionalEquality.NP

module Reflection.Param where

module Revelator (tyH : Type) where
    tm : Term → ℕ → Args → Term
    tm (pi (arg (arg-info v _) t₁) (el _ t₂)) y as = lam visible (tm t₂ (suc y) (mapVarArgs suc as ++ argʳ v (var 0 []) ∷ []))
    tm (var x args) = var
    tm (def f args) = var
    tm (sort s)     = var
    tm unknown _ _ = unknown
    tm (con c args) _ _ = opaque "revealator/tm/con: impossible" unknown
    tm (lam v ty) _ _ = opaque "revealator/tm/lam: impossible" unknown
    tm (lit l) _ _ = opaque "revealator/tm/lit: impossible" unknown
    tm (pat-lam cs args) _ _ = opaque "revealator/tm/pat-lam: TODO" unknown
    tÿpe : Type
    tÿpe = tyH `→ᵛʳ Reveal-args.tÿpe tyH
    term : Term
    term = lam visible (tm (unEl tyH) 0 [])
    fun : FunctionDef
    fun = fun-def tÿpe (clause (argᵛʳ var ∷ []) (tm (unEl tyH) 0 []) ∷ [])

data VarKind (n : ℕ) : Set where
  Kᵢ : Fin n → VarKind n
  Kᵣ : VarKind n

record Env (n : ℕ)(A B : Set) : Set where
  field
    pVar : VarKind n → A → B
    pCon : Name → Name
    pDef : Name → Name
open Env

Env' = λ n → Env n ℕ ℕ

ε : ∀ n → Env' n
ε n = record { pVar = λ _ _ → opaque "ε.pVar" 0
             ; pCon = const (opaque "ε.pCon" (quote ε))
             ; pDef = const (opaque "ε.pDef" (quote ε)) }

extDefEnv : ((Name → Name) → (Name → Name)) → ∀ {n A B} → Env n A B → Env n A B
extDefEnv ext Γ = record Γ { pDef = ext (pDef Γ) }

ext1DefEnv : (old new : Name) → ∀ {n A B} → Env n A B → Env n A B
ext1DefEnv old new = extDefEnv (λ f x → [yes: (λ _ → new) no: (λ _ → f x) ]′ (x ≟-Name old))

↑pVar : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
↑pVar zero = id
↑pVar (suc n) = ↑pVar n ∘ mapVar↑

on-pVar : ∀ {n A B C D} → (VarKind n → (A → B) → (C → D)) → Env n A B → Env n C D
on-pVar f Γ = record
  { pVar = λ k → f k (pVar Γ k)
  ; pCon = pCon Γ
  ; pDef = pDef Γ }

_+↑ : ∀ {n} → Env' n → Env' n
_+↑ {n} = on-pVar goK
  where
    goK : VarKind n → (ℕ → ℕ) → (ℕ → ℕ)
    goK (Kᵢ x) f = _+_ (n ∸ toℕ x) ∘ ↑pVar 1 (_+_ (toℕ x) ∘ f)
    goK Kᵣ     f = ↑pVar 1 (_+_ n ∘ f)

_+'_ : ∀ {w} → Env' w → ℕ → Env' w
Γ +' n = record { pVar = λ k → _+_ n ∘ pVar Γ k ; pCon = pCon Γ ; pDef = pDef Γ }

_+1 : ∀ {w} → Env' w → Env' w
Γ +1 = Γ +' 1

pattern `⟦zero⟧  = con (quote ⟦ℕ⟧.zero) []
pattern `⟦suc⟧ t = con (quote ⟦ℕ⟧.suc) (argᵛʳ t ∷ [])
pNat : ℕ → Term
pNat zero    = `⟦zero⟧
pNat (suc n) = `⟦suc⟧ (pNat n)

lam^ : ℕ → Visibility → Term → Term
lam^ zero    v x = x
lam^ (suc n) v x = lam v (lam^ n v x)

lam∈ : ∀ {n} → Env' n → (f : Env' n → Vec Term n → Term) → Term
lam∈ {n} Γ f = lam^ n visible (f (Γ +' n) (reverse (tabulate (λ x → var (toℕ x) []))))

app-tabulate : ∀ {n a} {A : Set a} → (Fin n → A) → List A → List A
app-tabulate {zero}  f xs = xs
app-tabulate {suc n} f xs = f zero ∷ app-tabulate (f ∘ suc) xs

p^args : ∀ {n A} → Relevance → (Fin n → A) → A → List (Arg A) → List (Arg A)
p^args r f x args = app-tabulate (λ k → argʰ r (f k)) (argᵛʳ x ∷ args)

p^lam : ℕ → Term → Term
p^lam n t = lam^ n hidden (lam visible t)

{-
pi^ : ℕ → Arg Type → Type → Type
pi^ zero    i t = t
pi^ (suc n) i t = `Π i (pi^ n i t)
-}

allVarsFrom : ∀ n → ℕ → Vec Term n
allVarsFrom zero    k = []
allVarsFrom (suc n) k = var (k + n) [] ∷ allVarsFrom n k

p3pi∈ : ∀ {n} (Γ : Env' n) (r : Relevance)
          (s : Type)
          (t : Env' n → Vec Term n → Type)
          (u : Env' n → Vec Term n → Type) → Term
p3pi∈ {n} Γ r s t u = unEl (go Γ (allFin n))
  where
  go : ∀ {m} → Env' n → Vec (Fin n) m → Type
  go Δ [] = 
      `Πᵛʳ (t Δ (allVarsFrom n 0)) (u (Γ +↑) (allVarsFrom n 1))
  go Δ (x ∷ xs) =
      `Π (argʰ r (mapVarType (pVar Δ (Kᵢ x)) s))
         (go (Δ +1) xs)

pSort∈ : ∀ {n} → Sort → Vec Term n → Type
pSort∈ s = go 0
  where
    go : ℕ → ∀ {n} → Vec Term n → Type
    go k []       = el (suc-sort s) (sort s)
    go k (t ∷ ts) = `Πᵛʳ (mapVarType (_+_ k) (el s t)) (go (suc k) ts)

pEnvPats : List (Arg Pattern) → ∀ {n} → Env' n → Env' n
pEnvPat : Pattern → ∀ {n} → Env' n → Env' n

pEnvPat (con _ pats) = pEnvPats pats
pEnvPat dot = id
pEnvPat var = _+↑
pEnvPat (lit _) = id
pEnvPat (proj _) = opaque "pEnvPats/proj" id
pEnvPat absurd = id

pEnvPats [] = id
pEnvPats (arg i p ∷ ps) = pEnvPat p ∘ pEnvPats ps

pPats : ∀ {n} → Env' n → List (Arg Pattern) → List (Arg Pattern)
pPat  : ∀ {n} → Env' n → Arg Pattern → List (Arg Pattern)

pPats Γ [] = []
pPats Γ (pat ∷ ps) = pPat Γ pat ++ pPats Γ ps

--nodot = var

pPat {n} Γ (arg (arg-info _ r) (con c pats))
  = p^args {n} r (const dot) (con (pCon Γ c) (pPats Γ pats)) []
pPat {n} Γ (arg (arg-info _ r) dot)
  = p^args {n} r (const dot) dot []
pPat {n} Γ (arg (arg-info _ r) var)
  = p^args {n} r (const var) var []
pPat {n} Γ (arg i (lit (nat l))) = opaque "pPat/lit/nat" []
pPat {n} Γ (arg (arg-info _ r) (lit l))
  = p^args {n} r go
                 (con (quote refl) []) []
      where
        go : ∀ {n} → Fin n → Pattern
        go zero = lit l
        go (suc _) = dot
pPat {n} Γ (arg (arg-info _ r) absurd) = p^args {n} r (const var) absurd []
pPat {n} Γ (arg i (proj p)) = opaque "pPat/proj" []

pLit : Literal → Term
pLit (nat n) = pNat n
pLit _       = con (quote refl) []

pTerm  : ∀ {n} → Env' n → Term → Term
pArgs  : ∀ {n} → Env' n → Args → Args
pType∈ : ∀ {n} → Env' n → Type             → Vec Term n → Type
pTerm∈ : ∀ {n} → Env' n → Term             → Vec Term n → Term
pPi∈   : ∀ {n} → Env' n → Arg Type → Type → Vec Term n → Term

pType∈ Γ (el s t) as = el s (pTerm∈ Γ t as)

pTerm {n} Γ (lam _ t) = p^lam n (pTerm (Γ +↑) t)
pTerm Γ (var v args)  = var (pVar Γ Kᵣ v) (pArgs Γ args)
pTerm Γ (con c args)  = con (pCon Γ c) (pArgs Γ args)
pTerm Γ (def d args)  = def (pDef Γ d) (pArgs Γ args)
pTerm Γ (lit l)       = pLit l
pTerm Γ (pat-lam _ _) = opaque "pTerm/pat-lam" unknown
pTerm Γ unknown       = unknown

pTerm Γ (sort s) = lam∈ Γ λ _ as → unEl (pSort∈ s as)
pTerm Γ (pi s t) = lam∈ Γ λ Δ → pPi∈ Δ s t

pPi∈ {n} Γ (arg (arg-info _ r) s) t as =
  p3pi∈ Γ r s (λ Δ → pType∈ Δ s) (λ Δ vs → pType∈ Δ t
    (vmap (λ a v → app (mapVar (_+_ (suc n)) a) (argᵛʳ v ∷ [])) as ⊛ vs))

pTerm∈ Γ (sort s) as = unEl (pSort∈ s as)
pTerm∈ Γ (pi s t) = pPi∈ Γ s t
pTerm∈ Γ t as = app (pTerm Γ t) (toList (vmap argᵛʳ as))

pArgs Γ [] = []
pArgs Γ (arg (arg-info _ r) t ∷ as)
  = p^args r (λ k → mapVar (pVar (Γ +↑) (Kᵢ k)) t) (pTerm Γ t) (pArgs Γ as)

pClause  : ∀ {n} → Env' n → Clause → Clause
pClauses : ∀ {n} → Env' n → Clauses → Clauses

pClause Γ (clause pats body) = clause (pPats Γ pats) (pTerm (pEnvPats pats Γ) body)
pClause Γ (absurd-clause pats) = absurd-clause (pPats Γ pats)

pClauses Γ [] = []
pClauses Γ (c ∷ cs) = pClause Γ c ∷ pClauses Γ cs

pFunDef : ∀ {n} → Env' n → Name → FunctionDef → FunctionDef
pFunDef Γ d (fun-def t cs)
  = fun-def (pType∈ Γ t (replicate (def d []))) (pClauses Γ cs)

postulate
  IMPOSSIBLE : FunctionDef

pFunName : ∀ {n} → Env' n → Name → FunctionDef
pFunName Γ x with definition x
... | function d = pFunDef Γ x d
... | _ = IMPOSSIBLE -- opaque "pFunName" (fun-def {!!} {!!})

pFunNameRec : ∀ {n} → Env' n → (x xₚ : Name) → FunctionDef
pFunNameRec Γ x xₚ = pFunName (ext1DefEnv x xₚ Γ) x

{-
pDefinition : Env' 2 → Name → Definition → Definition
pDefinition Γ n (function x) = function {!pFunDef!}
pDefinition Γ n (data-type x) = {!!}
pDefinition Γ n (record′ x) = {!!}
pDefinition Γ n constructor′ = {!!}
pDefinition Γ n axiom = {!!}
pDefinition Γ n primitive′ = {!!}

pName : Env' 2 → Name → Definition
pName Γ n = pDefinition Γ n (definition n)
-}

open import Data.String.Core using (String)
open import Data.Float       using (Float)

infixr 1 _[₀→₀]_
_[₀→₀]_ : ∀ {A : Set₀} (Aₚ : A → Set₀)
            {B : Set₀} (Bₚ : B → Set₀)
            (f : A → B) → Set₀
_[₀→₀]_ = λ {A} Aₚ {B} Bₚ f → ∀ {a} (aₚ : Aₚ a) → Bₚ (f a)

infixr 1 _[₀→₁]_
_[₀→₁]_ : ∀ {A : Set₀} (Aₚ : A → Set₀)
            {B : Set₁} (Bₚ : B → Set₁)
            (f : A → B) → Set₁
_[₀→₁]_ = λ {A} Aₚ {B} Bₚ f → ∀ {a} (aₚ : Aₚ a) → Bₚ (f a)

infixr 1 _[₁→₁]_
_[₁→₁]_ : ∀ {A : Set₁} (Aₚ : A → Set₁)
            {B : Set₁} (Bₚ : B → Set₁)
            (f : A → B) → Set₁
_[₁→₁]_ = λ {A} Aₚ {B} Bₚ f → ∀ {a} (aₚ : Aₚ a) → Bₚ (f a)

infixr 1 _[₁→₂]_
_[₁→₂]_ : ∀ {A : Set₁} (Aₚ : A → Set₁)
            {B : Set₂} (Bₚ : B → Set₂)
            (f : A → B) → Set₂
_[₁→₂]_ = λ {A} Aₚ {B} Bₚ f → ∀ {a} (aₚ : Aₚ a) → Bₚ (f a)

[[Set₀]] : ([Set₀] [₁→₂] [Set₁]) [Set₀]
[[Set₀]] = λ A → A [₀→₁] [Set₀]

{-
EqEnv = {!!}
EqRes = {!!}

eqTerm : EqEnv → Term → Term → EqRes
eqTerm Γ (var x args) (var x₁ args₁) = {!!}
eqTerm Γ (def f₀ args₀) (def f₁ args₁) = {!!}
eqTerm Γ (con c₀ args₀) (con c₁ args₁) = {!!}
eqTerm Γ (lam v t) (lam v' t') = {!!}
eqTerm Γ (pi t₁ t₂) (pi u₁ u₂) = {!!}
eqTerm Γ (sort s₀) (sort s₁) = {!!}
eqTerm Γ (lit l₀) (lit l₁) = {!!}
eqTerm Γ unknown unknown = {!!}
eqTerm Γ (def f args) u = {!!}
--eqTerm Γ (pat-lam cs args) u = {!!}
eqTerm _ _ = ?
-}

import Reflection.Simple as Si
open Si using (var;con;def;lam;pi;sort;unknown;simple;showTerm)

p[Set₀] = pFunName (ε 1) (quote [Set₀])
q[[Set₀]] = definition (quote [[Set₀]]) -- quoteTerm [[Set₀]]
test-type-p[Set₀] : ([Set₀] [₁→₂] [Set₁]) [Set₀] ≡ unquote (unEl (Get-type.from-fun-def p[Set₀]))
test-type-p[Set₀] = refl
test-term-p[Set₀] : quoteTerm [[Set₀]] ≡ Get-term.from-fun-def p[Set₀]
test-term-p[Set₀] = refl
unquoteDecl u-p[Set₀] = p[Set₀]

{-
p-[→]-type = unEl (Get-type.from-fun-def p-[→])
p-[→]' : ∀ {A : Set₀}       (A₀ₚ : A → Set₀)
                {Aₚ : A → Set₀} (A₁ₚ : {x : A} → A₀ₚ x → Set₀)
                {B : Set₀}       (B₀ₚ : B → Set₀)
                {Bₚ : B → Set₀} (B₁ₚ : {x : B} → B₀ₚ x → Set₀)
                {f : A → B}    (fₚ : {x : A} → A₀ₚ x → B₀ₚ (f x))
              → (Aₚ [₀→₀] Bₚ) f →
              {C : Set₀} → (C → Set₀) → {t : {!!}} → (A → B) → Set₀ -- _[₀→₀]_ {A} {-A₀ₚ} {Aₚ-} {-A₁ₚ-} {!!} {B} {!!} {-B₀ₚ} B₁ₚ-} f -- fₚ
p-[→]' = {!unquote (Get-term.from-fun-def p-[→])!}
-}

[String] : [★₀] String
[String] _ = 𝟙

[Float] : [★₀] Float
[Float] _ = 𝟙

⟦String⟧ : ⟦★₀⟧ String String
⟦String⟧ = _≡_

⟦Float⟧ : ⟦★₀⟧ Float Float
⟦Float⟧ = _≡_

data [𝟚] : [Set₀] 𝟚 where
  [0₂] : [𝟚] 0₂
  [1₂] : [𝟚] 1₂

data [ℕ] : [Set₀] ℕ where
  [zero] : [ℕ] zero
  [suc]  : ([ℕ] [→] [ℕ]) suc

[pred] : ([ℕ] [→] [ℕ]) pred
[pred] [zero]     = [zero]
[pred] ([suc] xₚ) = xₚ

revealed-[→] = Reveal-args.nåme (quote _[₀→₀]_)
unquoteDecl revealed-[→]' = un-function revealed-[→]

unquoteDecl revelator-[→] = Revelator.fun (type (quote _[₀→₀]_))

{-
p-[→] = pFunName (ε 1) (quote _[₀→₀]_)
p-[→]-type = unEl (Get-type.from-fun-def p-[→])

{-
p-[→]' : (x0 : Set) → (x1 : (x1 : x0) → Set) → (x2 : (x2 : x0) → Set) → (x3 : (x3 : x0) → (x4 : x1 x3) → (x5 : x2 x3) → Set) → (x4 : Set) → (x5 : (x5 : x4) → Set) → (x6 : (x6 : x4) → Set) → (x7 : (x7 : x4) → (x8 : x5 x7) → (x9 : x6 x7) → Set) → (x8 : (x8 : x0) → x4) → (x9 : (x9 : x0) → (x10 : x1 x9) → x5 (x8 x9)) → (x10 : _[₀→₀]_ {x0} x2 {x4} x6 x8) → Set
{-
p-[→]' : ∀ {A : Set₀}       (A₀ₚ : A → Set₀)
                {Aₚ : A → Set₀} (A₁ₚ : {x : A} → A₀ₚ x → Set₀)
                {B : Set₀}       (B₀ₚ : B → Set₀)
                {Bₚ : B → Set₀} (B₁ₚ : {x : B} → B₀ₚ x → Set₀)
                {f : A → B}    (fₚ : {x : A} → A₀ₚ x → B₀ₚ (f x))
              → (Aₚ [₀→₀] Bₚ) f →
              {C : Set₀} → (C → Set₀) → {t : {!!}} → (A → B) → Set₀ -- _[₀→₀]_ {A} {-A₀ₚ} {Aₚ-} {-A₁ₚ-} {!!} {B} {!!} {-B₀ₚ} B₁ₚ-} f -- fₚ
-}
p-[→]' = {!unquote (Get-term.from-fun-def p-[→])!}

test : {!showTerm p-[→]-type!}
test = {!unquote (Get-term.from-fun-def p-[→])!}
-}
-- unquoteDecl _[[→]]_ = p-[→]

{-
data [[ℕ]] : [[Set₀]] [ℕ] [ℕ] where
  [[zero]] : [[ℕ]] [zero] [zero]
  [[suc]]  : ([[ℕ]] [[→]] [[ℕ]]) [suc] [suc]
-}

defDefEnv1 : Name → Name
defDefEnv1 (quote 𝟚) = quote [𝟚]
defDefEnv1 (quote ℕ) = quote [ℕ]
defDefEnv1 (quote String) = quote [String]
defDefEnv1 (quote Float) = quote [Float]
defDefEnv1 (quote ★₀) = quote [★₀]
defDefEnv1 (quote ★₁) = quote [★₁]
defDefEnv1 n         = opaque "defDefEnv1" n

defConEnv1 : Name → Name
defConEnv1 (quote 0₂) = quote [0₂]
defConEnv1 (quote 1₂) = quote [1₂]
defConEnv1 (quote ℕ.zero) = quote [zero]
defConEnv1 (quote ℕ.suc)  = quote [suc]
defConEnv1 n              = opaque "defConEnv1" n

defDefEnv2 : Name → Name
defDefEnv2 (quote 𝟚) = quote ⟦𝟚⟧
defDefEnv2 (quote ℕ) = quote ⟦ℕ⟧
defDefEnv2 (quote String) = quote ⟦String⟧
defDefEnv2 (quote Float) = quote ⟦Float⟧
defDefEnv2 (quote ★₀) = quote ⟦★₀⟧
defDefEnv2 (quote ★₁) = quote ⟦★₁⟧
defDefEnv2 n         = opaque "defDefEnv" n

defConEnv2 : Name → Name
defConEnv2 (quote 0₂) = quote ⟦0₂⟧
defConEnv2 (quote 1₂) = quote ⟦1₂⟧
defConEnv2 (quote ℕ.zero) = quote ⟦ℕ⟧.zero
defConEnv2 (quote ℕ.suc)  = quote ⟦ℕ⟧.suc
defConEnv2 n              = opaque "defConEnv2" n

defEnv0 : Env' 0
defEnv0 = record { pVar = λ _ _ → opaque "defEnv1.pVar" 0
                 ; pCon = id
                 ; pDef = id }

defEnv1 : Env' 1
defEnv1 = record { pVar = λ _ _ → opaque "defEnv1.pVar" 0
                 ; pCon = defConEnv1
                 ; pDef = defDefEnv1 }

defEnv2 : Env' 2
defEnv2 = record { pVar = λ _ _ → opaque "defEnv2.pVar" 0
                 ; pCon = defConEnv2
                 ; pDef = defDefEnv2 }

{-
_⟦+⟧_ : (⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧) _+_ _+_
zero  ⟦+⟧ n = n
suc m ⟦+⟧ n = suc (m ⟦+⟧ n)
-}

_/2 : ℕ → ℕ
zero        /2 = zero
suc zero    /2 = zero
suc (suc n) /2 = suc (n /2)

_⟦/2⟧ : (⟦ℕ⟧ ⟦₀→₀⟧ ⟦ℕ⟧) _/2 _/2
⟦zero⟧         ⟦/2⟧ = ⟦zero⟧
⟦suc⟧ ⟦zero⟧    ⟦/2⟧ = ⟦zero⟧
⟦suc⟧ (⟦suc⟧ n) ⟦/2⟧ = ⟦suc⟧ (n ⟦/2⟧)

_+ℕ_ : ℕ → ℕ → ℕ
zero  +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

_⟦+ℕ⟧_ : (⟦ℕ⟧ ⟦₀→₀⟧ ⟦ℕ⟧ ⟦₀→₀⟧ ⟦ℕ⟧) _+ℕ_ _+ℕ_
⟦zero⟧  ⟦+ℕ⟧ n = n
⟦suc⟧ m ⟦+ℕ⟧ n = ⟦suc⟧ (m ⟦+ℕ⟧ n)

⟦⟦Set₀⟧⟧ : (⟦Set₀⟧ ⟦₁→₂⟧ ⟦Set₀⟧ ⟦₁→₂⟧ ⟦Set₁⟧) ⟦Set₀⟧ ⟦Set₀⟧
⟦⟦Set₀⟧⟧ = λ A₀ A₁ → A₀ ⟦₀→₁⟧ A₁ ⟦₀→₁⟧ ⟦Set₀⟧

⟦⟦Set₀⟧⟧' : {x₁ x₂ : Set} (xᵣ : x₁ → x₂ → Set) {x₃ : Set} {x₄ : Set}
            (xᵣ₁ : x₃ → x₄ → Set) →
            (x₁ → x₃ → Set) → (x₂ → x₄ → Set) → Set₁
⟦⟦Set₀⟧⟧' = λ A₀ A₁ f₁ f₂ →
  ∀ {x₁} {x₂} (xᵣ : A₀ x₁ x₂)
    {x₃} {x₄} (xᵣ₁ : A₁ x₃ x₄) →
    f₁ x₁ x₃ → f₂ x₂ x₄ → Set

-- Since quoteTerm normalises
test-⟦⟦Set₀⟧⟧ : quoteTerm ⟦⟦Set₀⟧⟧ ≡ quoteTerm ⟦⟦Set₀⟧⟧'
test-⟦⟦Set₀⟧⟧ = refl

⟦⟦Set₀⟧⟧-type = unquote (unEl (type (quote ⟦⟦Set₀⟧⟧)))
test-⟦⟦Set₀⟧⟧-type : ⟦⟦Set₀⟧⟧-type ≡ unquote (unEl (type (quote ⟦⟦Set₀⟧⟧')))
test-⟦⟦Set₀⟧⟧-type = refl

pSet₀ = pTerm defEnv2 `★₀
ppSet₀ = pTerm defEnv2 pSet₀
p⟦Set₀⟧ = pFunName defEnv2 (quote ⟦Set₀⟧)
test-pSet₀ : pSet₀ ≡ quoteTerm ⟦Set₀⟧
test-pSet₀ = refl
test-ppSet₀ : ppSet₀ ≡ quoteTerm ⟦⟦Set₀⟧⟧
test-ppSet₀ = refl
test-ppSet₀'' : ppSet₀ ≡ Get-term.from-fun-def p⟦Set₀⟧
test-ppSet₀'' = refl

unquoteDecl ⟦⟦Set₀⟧⟧'' = p⟦Set₀⟧
test-⟦⟦Set₀⟧⟧'' : _≡_ {A = ⟦⟦Set₀⟧⟧-type} ⟦⟦Set₀⟧⟧'' ⟦⟦Set₀⟧⟧
test-⟦⟦Set₀⟧⟧'' = refl

test-p0-⟦Set₀⟧ : pTerm defEnv0 (quoteTerm ⟦Set₀⟧) ≡ quoteTerm ⟦Set₀⟧
test-p0-⟦Set₀⟧ = refl

data ⟦⟦𝟚⟧⟧ : (⟦⟦Set₀⟧⟧ ⟦𝟚⟧ ⟦𝟚⟧) ⟦𝟚⟧ ⟦𝟚⟧ where
  ⟦⟦0₂⟧⟧ : ⟦⟦𝟚⟧⟧ ⟦0₂⟧ ⟦0₂⟧ ⟦0₂⟧ ⟦0₂⟧
  ⟦⟦1₂⟧⟧ : ⟦⟦𝟚⟧⟧ ⟦1₂⟧ ⟦1₂⟧ ⟦1₂⟧ ⟦1₂⟧

_≡clauses_ = λ x y → Get-clauses.from-def x ≡ Get-clauses.from-def y
_≡type_ = λ x y → Get-type.from-def x ≡ Get-type.from-def y
  
module Test where
  p1ℕ→ℕ = pTerm defEnv1 (quoteTerm (ℕ → ℕ))
  [ℕ→ℕ] = [ℕ] [→] [ℕ]
  test-p1ℕ→ℕ : unquote p1ℕ→ℕ ≡ [ℕ→ℕ]
  test-p1ℕ→ℕ = refl

  p2ℕ→ℕ = pTerm defEnv2 (quoteTerm (ℕ → ℕ))
  ⟦ℕ→ℕ⟧ = ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧
  test-p2ℕ→ℕ : unquote p2ℕ→ℕ ≡ ⟦ℕ→ℕ⟧
  test-p2ℕ→ℕ = refl

  pℕ→ℕ→ℕ = pTerm defEnv2 (quoteTerm (ℕ → ℕ → ℕ))
  ⟦ℕ→ℕ→ℕ⟧ = ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧
  test-pℕ→ℕ→ℕ : pℕ→ℕ→ℕ ≡ quoteTerm ⟦ℕ→ℕ→ℕ⟧
  test-pℕ→ℕ→ℕ = refl
  ZERO : Set₁
  ZERO = (A : Set₀) → A
  ⟦ZERO⟧ : ZERO → ZERO → Set₁
  ⟦ZERO⟧ f₀ f₁ =
    {A₀ A₁ : Set₀} (Aᵣ : A₀ → A₁ → Set₀)
    → Aᵣ (f₀ A₀) (f₁ A₁)
  pZERO = pTerm (ε 2) (quoteTerm ZERO)
  q⟦ZERO⟧ = quoteTerm ⟦ZERO⟧
  test-pZERO : pZERO ≡ q⟦ZERO⟧
  test-pZERO = refl
  ID : Set₁
  ID = (A : Set₀) → A → A
  ⟦ID⟧ : ID → ID → Set₁
  ⟦ID⟧ f₀ f₁ =
    {A₀ A₁ : Set₀} (Aᵣ : A₀ → A₁ → Set₀)
    {x₀ : A₀} {x₁ : A₁} (x : Aᵣ x₀ x₁)
    → Aᵣ (f₀ A₀ x₀) (f₁ A₁ x₁)
  pID = pTerm (ε 2) (quoteTerm ID)
  q⟦ID⟧ = quoteTerm ⟦ID⟧
  test-param : absTerm q⟦ID⟧ ≡ absTerm pID
  test-param = refl
  test-ID : q⟦ID⟧ ≡ pID
  test-ID = refl

  p-not = pFunName defEnv2 (quote not)
  unquoteDecl P-not = p-not
  test-not : ∀ {x₀ x₁ : 𝟚} (xᵣ : ⟦𝟚⟧ x₀ x₁) → ⟦not⟧ xᵣ ≡ P-not xᵣ
  test-not ⟦0₂⟧ = refl
  test-not ⟦1₂⟧ = refl

  p1-pred = pFunName defEnv1 (quote pred)
  q-[pred] = quoteTerm [pred]
  unquoteDecl [pred]' = p1-pred
  test-p1-pred : ∀ {n} (nₚ : [ℕ] n) → [pred]' nₚ ≡ [pred] nₚ
  test-p1-pred [zero] = refl
  test-p1-pred ([suc] nₚ) = refl

  p2-pred = pFunName defEnv2 (quote pred)
  q-⟦pred⟧ = definition (quote ⟦pred⟧)
  unquoteDecl ⟦pred⟧' = p2-pred
  test-p2-pred : ∀ {n₀ n₁} (nᵣ : ⟦ℕ⟧ n₀ n₁) → ⟦pred⟧' nᵣ ≡ ⟦pred⟧ nᵣ
  test-p2-pred ⟦zero⟧ = refl
  test-p2-pred (⟦suc⟧ nᵣ) = refl

  p/2 = pFunNameRec defEnv2 (quote _/2)
  q⟦/2⟧ = definition (quote _⟦/2⟧)
  unquoteDecl _⟦/2⟧' = p/2 _⟦/2⟧'
  test-/2 : function (p/2 (quote _⟦/2⟧)) ≡ q⟦/2⟧
  test-/2 = refl
  test-/2' : ∀ {n₀ n₁} (nᵣ : ⟦ℕ⟧ n₀ n₁) → nᵣ ⟦/2⟧' ≡ nᵣ ⟦/2⟧
  test-/2' ⟦zero⟧ = refl
  test-/2' (⟦suc⟧ ⟦zero⟧) = refl
  test-/2' (⟦suc⟧ (⟦suc⟧ nᵣ)) = ap ⟦suc⟧ (test-/2' nᵣ)

  p+ = pFunNameRec defEnv2 (quote _+ℕ_)
  q⟦+⟧ = definition (quote _⟦+ℕ⟧_)
  unquoteDecl _⟦+⟧'_ = p+ _⟦+⟧'_
  test-+ : function (p+ (quote _⟦+ℕ⟧_)) ≡ q⟦+⟧
  test-+ = refl
  test-+' : ∀ {n₀ n₁} (nᵣ : ⟦ℕ⟧ n₀ n₁) {n'₀ n'₁} (n'ᵣ : ⟦ℕ⟧ n'₀ n'₁) → nᵣ ⟦+⟧' n'ᵣ ≡ nᵣ ⟦+ℕ⟧ n'ᵣ
  test-+' ⟦zero⟧    n'ᵣ = refl
  test-+' (⟦suc⟧ nᵣ) n'ᵣ = ap ⟦suc⟧ (test-+' nᵣ n'ᵣ)

  {-
  is-good : String → 𝟚
  is-good "good" = 1₂
  is-good _      = 0₂

  ⟦is-good⟧ : (⟦String⟧ ⟦₀→₀⟧ ⟦𝟚⟧) is-good is-good
  ⟦is-good⟧ {"good"} refl = ⟦1₂⟧
  ⟦is-good⟧ {_}      refl = {!!}

  p-is-good = pFunName defEnv2 (quote is-good)
  unquoteDecl ⟦is-good⟧' = p-is-good
  test-is-good = {!!}
  -}

-- -}
-- -}
-- -}
-- -}
-- -}
