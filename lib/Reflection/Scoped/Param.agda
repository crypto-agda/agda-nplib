open import Relation.Binary.Logical
open import Data.Nat.Logical
open import Function
open import Opaque
open import Data.Zero
open import Data.One
open import Data.Nat
open import Data.List
open import Data.Sum.NP
import Reflection.NP as R
open R using (Name; Arg; arg; Arg-info; arg-info; Literal; Visibility; visible; hidden; Relevance; relevant; irrelevant; Pattern; argᵛʳ; argʰʳ; absTerm; Abs; module Abs; _,_)
open import Reflection.Scoped as S
open import Reflection.Scoped.Translation as T

module Reflection.Scoped.Param where

data VarKind : Set where
  K₀ K₁ Kᵣ : VarKind

record Env (A B : Set) : Set where
  field
    pVar : VarKind → A → B
    pCon : Name → Name
    pDef : Name → Name
open Env

ε : ∀ {B} → Env 𝟘 B
ε = record { pVar = λ _ ()
           ; pCon = const (opaque "ε.pCon" (quote ε))
           ; pDef = const (opaque "ε.pDef" (quote ε)) }

defDefEnv : Name → Name
defDefEnv (quote ℕ) = quote ⟦ℕ⟧
defDefEnv n         = opaque "defDefEnv" n

defConEnv : Name → Name
defConEnv (quote ℕ.zero) = quote ⟦ℕ⟧.zero
defConEnv (quote ℕ.suc)  = quote ⟦ℕ⟧.suc
defConEnv n              = opaque "defConEnv" n

defEnv : ∀ {B} → Env 𝟘 B
defEnv = record { pVar = λ _ ()
                ; pCon = defConEnv
                ; pDef = defDefEnv }

_⊎𝟙^_ : Set → ℕ → Set
A ⊎𝟙^ 0       = A
A ⊎𝟙^ (suc n) = (A ⊎𝟙^ n) ⊎ 𝟙

inl^ : ∀ n {A} → A → A ⊎𝟙^ n
inl^ 0 x = x
inl^ (suc n) x = inl (inl^ n x)

# : ∀ n {A} → A ⊎𝟙^ (suc n)
# 0       = inr 0₁
# (suc n) = inl (# n)

on-pVar : ∀ {A B C D} → (VarKind → (A → B) → (C → D)) → Env A B → Env C D
on-pVar f Γ = record
  { pVar = λ k → f k (pVar Γ k)
  ; pCon = pCon Γ
  ; pDef = pDef Γ }

_+1 : ∀ {A B} → Env A B → Env A (B ⊎ 𝟙)
_+1 = on-pVar λ k f → inl ∘ f

_+2 : ∀ {A B} → Env A B → Env A (B ⊎𝟙^ 2)
Γ +2 = Γ +1 +1

_+3 : ∀ {A B} → Env A B → Env A (B ⊎𝟙^ 3)
Γ +3 = Γ +2 +1

_↑1 : ∀ {A B} → Env A B → Env (A ⊎ 𝟙) (B ⊎ 𝟙)
_↑1 = on-pVar λ k → Map.↑

_\3 : ∀ {A B} → Env A B → Env (A ⊎ 𝟙) (B ⊎𝟙^ 3)
_\3 = on-pVar λ { K₀ f → inl^ 2 ∘ Map.↑ f
                ; K₁ f → inl ∘ Map.↑ (inl ∘ f)
                ; Kᵣ f → Map.↑ (inl^ 2 ∘ f) }

pW : ∀ {A B}(Γ : Env A B)
       (f : (Δ : Env A (B ⊎𝟙^ 2))(a₀ a₁ : Term (B ⊎𝟙^ 2)) → Term (B ⊎𝟙^ 2))
     → Term B
pW Γ f = lam visible (lam visible (f (Γ +2) (var (# 1) []) (var (# 0) [])))

pTerm  : ∀ {A B}(Γ : Env A B)(t : Term A)  → Term B
pArgs  : ∀ {A B}(Γ : Env A B)(a : Args A)  → Args B
pLit   : ∀ {A B}(Γ : Env A B)(l : Literal) → Term B
pType∈ : ∀ {A B}(Γ : Env A B)(t : Type A)(a₀ a₁ : Term B) → Type B
pTerm∈ : ∀ {A B}(Γ : Env A B)(t : Term A)(a₀ a₁ : Term B) → Term B
pSort∈ : ∀ {A B}(Γ : Env A B)(s : Sort A)(a₀ a₁ : Term B) → Term B
pPi∈   : ∀ {A B}(Γ : Env A B)(t : Arg (Type A))(u : Scope 𝟙 Type A)(a₀ a₁ : Term B) → Term B

pTerm Γ (lam _ t) = lam hidden (lam hidden (lam visible (pTerm (Γ \3) t)))
pTerm Γ (var v args) = var (pVar Γ Kᵣ v) (pArgs Γ args)
pTerm Γ (con c args) = con (pCon Γ c) (pArgs Γ args)
pTerm Γ (def d args) = def (pDef Γ d) (pArgs Γ args)
pTerm Γ (lit l) = pLit Γ l
-- pTerm Γ (pat-lam cs args) = unknown -- TODO
pTerm Γ unknown = unknown

pTerm Γ (sort s) = pW Γ λ Δ → pSort∈ Δ s
pTerm Γ (pi s t) = pW Γ λ Δ → pPi∈ Δ s t

-- pTerm Γ t as' = opaque "impossible: a type cannot be applied to arguments" unknown

pPi∈ Γ (arg (arg-info _ r) s) t a₀ a₁ =
  pi (arg (arg-info hidden r) (Map.tÿpe (pVar Γ K₀) s)) $
  `Π (arg (arg-info hidden r) (Map.tÿpe (pVar (Γ +1) K₁) s)) $
  `Π (arg (arg-info visible relevant)
          (pType∈ (Γ +2) s (var (# 1) []) (var (# 0) [])))
  (pType∈ (Γ \3) t
    (app (Map.term (inl^ 3) a₀) (argᵛʳ (var (# 2) []) ∷ []))
    (app (Map.term (inl^ 3) a₁) (argᵛʳ (var (# 1) []) ∷ [])))

pTerm∈ Γ (sort s) = pSort∈ Γ s
pTerm∈ Γ (pi s t) = pPi∈ Γ s t
pTerm∈ Γ t a₀ a₁ = app (pTerm Γ t) (argᵛʳ a₀ ∷ argᵛʳ a₁ ∷ [])

pLit  Γ l  = unknown -- TODO
pArgs Γ [] = []
pArgs Γ (arg (arg-info _ r) t ∷ as)
  = arg (arg-info hidden  r) (opaque "t0" (Map.term (pVar Γ K₀)) t)
  ∷ arg (arg-info hidden  r) (opaque "t1" (Map.term (pVar Γ K₁)) t)
  ∷ arg (arg-info visible relevant) (pTerm Γ t)
  ∷ pArgs Γ as
pSort∈ Γ (lit n) a₀ a₁ = piᵛʳ (el (lit n) a₀)
                            (`Πᵛʳ (el (lit n) (Map.term inl a₁)) ``★₀)
pSort∈ Γ (set t) _ _ = unknown -- TODO
pSort∈ Γ unknown _ _ = unknown

pType∈ Γ (el (lit n) t) a₀ a₁ = el (lit n) (pTerm∈ Γ t a₀ a₁)
pType∈ Γ (el s t)       _ _  = el unknown unknown

{-
pClause : ∀ {A B} → Env A B → Clause A → Clause B
pClause Γ c = ?
-}

open import Relation.Binary.PropositionalEquality
module Test' where

    param : R.Term → R.Term
    param t = T.SR.term T.SR.ε (pTerm defEnv (T.RS.term T.RS.ε t))
    --  test-lift : lift 
    pℕ→ℕ = param (quoteTerm (ℕ → ℕ))
    ⟦ℕ→ℕ⟧ = ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧
    test-pℕ→ℕ : unquote pℕ→ℕ ≡ ⟦ℕ→ℕ⟧
    test-pℕ→ℕ = refl
    pℕ→ℕ→ℕ = param (quoteTerm (ℕ → ℕ → ℕ))
    ⟦ℕ→ℕ→ℕ⟧ = ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦ℕ⟧
    test-pℕ→ℕ→ℕ : pℕ→ℕ→ℕ ≡ quoteTerm ⟦ℕ→ℕ→ℕ⟧
    test-pℕ→ℕ→ℕ = refl
    ZERO : Set₁
    ZERO = (A : Set₀) → A
    ⟦ZERO⟧ : ZERO → ZERO → Set₁
    ⟦ZERO⟧ f₀ f₁ =
        {A₀ A₁ : Set₀} (Aᵣ : A₀ → A₁ → Set₀)
        → Aᵣ (f₀ A₀) (f₁ A₁)
    pZERO = param (quoteTerm ZERO)
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
    pID = param (quoteTerm ID)
    q⟦ID⟧ = quoteTerm ⟦ID⟧
    test-ID-abs : absTerm q⟦ID⟧ ≡ absTerm pID
    test-ID-abs = refl
    test-param : q⟦ID⟧ ≡ pID
    test-param = refl

    test-opaque : opaque "a" "" ≡ opaque "a" ""
    test-opaque = refl
-- -}
-- -}
-- -}
-- -}
-- -}
