open import Reflection.NP hiding (app)
open import Function
open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.List hiding (_++_)
open import Data.String
open import Data.Float
open import Data.Char

module Reflection.Simple where

data Var A : Set where
  var : (x : A) → Var A
  con : (c : Name) → Var A
  def : (f : Name) → Var A

data Tm A : Set where
  app     : (v : Var A) (args : List (Tm A)) → Tm A
  lam     : (s : A) (t : Tm A) → Tm A
  pi      : (s : A) (t₁ : Tm A) (t₂ : Tm A) → Tm A
  sort    : ℕ → Tm A
  lit     : (l : Literal) → Tm A
  unknown : Tm A

Tms : Set → Set
Tms A = List (Tm A)

module Level where
    Env : Set
    Env = ℕ
    vår : Env → Var ℕ → Var ℕ
    vår depth (var ix) = var (depth ∸ suc ix)
    vår depth (con c)  = con c
    vår depth (def d)  = def d
    term  : Env → Tm ℕ → Tm ℕ
    terms : Env → Tms ℕ → Tms ℕ
    term Γ (app x args) = app (vår Γ x) (terms Γ args)
    term Γ (lam _ t) = lam Γ (term (suc Γ) t)
    term Γ (pi _ t t₁) = pi Γ (term Γ t) (term (suc Γ) t₁)
    term Γ (sort l) = sort l
    term Γ (lit l) = lit l
    term Γ unknown = unknown
    terms Γ [] = []
    terms Γ (x ∷ ts) = term Γ x ∷ terms Γ ts

module Simplify where
    term : Term → Tm ℕ
    tÿpe : Type → Tm ℕ
    årgs : Args → List (Tm ℕ)
    term (var x args) = app (var x) (årgs args)
    term (con c args) = app (con c) (årgs args)
    term (def f args) = app (def f) (årgs args)
    term (lam v t) = lam 42 (term t)
    term (pat-lam cs args) = unknown
    term (pi (arg _ t₁) t₂) = pi 42 (tÿpe t₁) (tÿpe t₂)
    term (sort (lit l)) = sort l
    term (sort _) = unknown
    term (lit l) = lit l
    term unknown = unknown
    tÿpe (el s t) = term t
    årgs [] = []
    årgs (arg i x ∷ as) = term x ∷ årgs as

simple : Term → Tm ℕ
simple = Level.term 0 ∘ Simplify.term

open import Text.Printer
module Printer where
    open PrEnv

    topᴸ = mk 2
    appᴸ = mk 1
    atmᴸ = mk 0

    prTm : PrEnv → Pr (Tm ℕ)
    prV   : Pr ℕ
    prVar : Pr (Var ℕ)
    prTms : Pr (Tms ℕ)

    prV x = ` "x" ∘ `(showNat x)

    prVar (var x) = prV x
    prVar (con c) = `(showName c)
    prVar (def f) = `(showName f)

    prTm ℓ (lam b t)  = paren topᴸ ℓ (` "λ" ∘ prV b ∘ ` ". " ∘ prTm topᴸ t)
    prTm ℓ (app v []) = prVar v
    prTm ℓ (app v as) = paren appᴸ ℓ (prVar v ∘ prTms as)
    prTm ℓ (pi s t u) = paren topᴸ ℓ (` "(" ∘ prV s ∘ ` " : " ∘ prTm topᴸ t ∘ ` ") → " ∘ prTm topᴸ u)
    prTm ℓ (sort l)   = ` "Set" ∘ ` showNat l
    prTm ℓ (lit l)    = `(showLiteral l)
    prTm ℓ unknown    = ` "unknown"

    prTms [] = id
    prTms (a ∷ as) = ` " " ∘ prTm atmᴸ a ∘ prTms as

showTerm : Term → String
showTerm t = prTm topᴸ (simple t) "" where open Printer

showType = showTerm ∘ unEl
