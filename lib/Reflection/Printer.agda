open import Reflection.NP hiding (app)
open import Function
open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.List hiding (_++_)
open import Data.String
open import Data.Product
open import Data.Float
open import Data.Char
open import Data.Bool
open import Relation.Nullary.Decidable
open import Category.Monad
open import Category.Monad.State

module Reflection.Printer where

data Tm (A B : Set) : Set where
  var     : (x : B) (args : List (Arg (Tm A B))) → Tm A B
  -- Constructor applied to arguments.
  con     : (c : Name) (args : List (Arg (Tm A B))) → Tm A B
  -- Identifier applied to arguments.
  def     : (f : Name) (args : List (Arg (Tm A B))) → Tm A B
  -- Different kinds of λ-abstraction.
  lam     : (x : A) (v : Visibility) (t : Abs (Tm A B)) → Tm A B
  -- Pattern matching λ-abstraction.
--  pat-lam : (cs : List Clause) (args : List (Arg (Tm A B))) → Tm A B
  -- Pi-type.
  pi      : (x : A) (t₁ : Arg (Tm A B)) (t₂ : Abs (Tm A B)) → Tm A B
  -- A sort.
  -- sort    : (s : Sort) → Tm A B
  sort    : (level : ℕ) → Tm A B
  -- A literal.
  lit     : (l : Literal) → Tm A B
  -- Anything else.
  unknown : Tm A B

Tms : (A B : Set) → Set
Tms A B = List (Arg (Tm A B))

module Level where
    Env : Set
    Env = ℕ
    vår : Env → ℕ → ℕ
    vår depth ix = depth ∸ suc ix
    term  : Env → Term → Tm ℕ ℕ
    term-arg : Env → Arg Term → Arg (Tm ℕ ℕ)
    term-args : Env → List (Arg Term) → List (Arg (Tm ℕ ℕ))
    tÿpe : Env → Type → Tm ℕ ℕ
    tÿpe-arg : Env → Arg Type → Arg (Tm ℕ ℕ)
    term Γ (var x args) = var (vår Γ x) (term-args Γ args)
    term Γ (con c args) = con c (term-args Γ args)
    term Γ (def d args) = def d (term-args Γ args)
    term Γ (lam v (abs s t)) = lam Γ v (abs s (term (suc Γ) t))
    term Γ (pi t (abs s t₁)) = pi Γ (tÿpe-arg Γ t) (abs s (tÿpe (suc Γ) t₁))
    term Γ (sort (lit l)) = sort l
    term Γ (sort _) = unknown
    term Γ (lit l) = lit l
    term Γ unknown = unknown
    term Γ (pat-lam _ _) = unknown
    tÿpe Γ (el s t) = term Γ t
    tÿpe-arg Γ (arg i t) = arg i (tÿpe Γ t)
    term-arg Γ (arg i t) = arg i (term Γ t)
    term-args Γ [] = []
    term-args Γ (x ∷ ts) = term-arg Γ x ∷ term-args Γ ts
    
    open RawMonadState (StateMonadState Env)

    pat  : Pattern → State Env Pattern
    pats : Pats    → State Env Pats

    bump = get >>= λ Γ → put (Γ + 1) >> return Γ

    pat (con c ps) = pats ps >>= λ ps' → return (con c ps')
    pat dot      = bump >> return dot
    pat (var s)  = bump >>= λ Γ → return (var ("x" ++ showNat Γ))
    pat (lit l)  = return (lit l)
    pat (proj p) = return (proj p)
    pat absurd   = return absurd
    
    pats []             = return []
    pats (arg i p ∷ ps) = pat p >>= λ p' →
                          pats ps >>= λ ps' →
                          return (arg i p' ∷ ps')

open import Text.Printer hiding (paren)
module Printer (showName' : Name → String) where
    open PrEnv
    
    Showᴸ : Set
    Showᴸ = PrEnv → ShowS
    
    Prᴸ : Set → Set
    Prᴸ A = A → Showᴸ
    
    showOf : ∀ {A : Set} → (A → ShowS) → A → String
    showOf f x = f x ""

    paren : Showᴸ → (target current : PrEnv) → ShowS
    paren s target current = if ⌊ level target ≤? level current ⌋ then s current else parenBase (s target)
    
    _`sepBy`_ : List ShowS → ShowS → ShowS
    []       `sepBy` s = id
    (x ∷ xs) `sepBy` s = go x xs
      where go : ShowS → List ShowS → ShowS
            go x0 []       = x0
            go x0 (y ∷ ys) = x0 ∘ s ∘ go y ys

    topᴸ = mk 2
    appᴸ = mk 1
    atmᴸ = mk 0
    
    paren-visibility : Visibility → Showᴸ → (target current : PrEnv) → ShowS
    paren-visibility visible   p target current = paren p target current
    paren-visibility hidden    p target current = `"{"  ∘ p target ∘ `"}"
    paren-visibility instance′ p target current = `"{{" ∘ p target ∘ `"}}"

    -- test = {!!}

    ``_ : String → Showᴸ
    ``_ s _ = ` s
    
    {-Tm' = Tm ℕ String
    Tms' = Tms ℕ String
    -}
    Tm' = Tm ℕ ℕ
    Tms' = Tms ℕ ℕ

    prTm   : Prᴸ Tm'
    prTms  : Pr Tms'
    prV    : String → Pr ℕ
    prApp  : ShowS → Prᴸ Tms'
    prLam  : String → ℕ → Visibility → ShowS
    prLams : Prᴸ Tm'

    prV s x = ` "x" ∘ `(showNat x)
    
    prApp pV [] = const pV
    prApp pV xs = paren (λ _ → pV ∘ prTms xs) appᴸ

    prTm (lam b v (abs s t)) = paren (λ ℓ → ` "λ " ∘ prLam s b v ∘ prLams t topᴸ) topᴸ
    prTm (var v as)  = prApp (prV "x" v)     as
    prTm (con c as)  = prApp (`(showName' c)) as
    prTm (def d as)  = prApp (`(showName' d)) as
    prTm (pi x (arg (arg-info v r) t) (abs s u))
      = paren (λ ℓ → paren-visibility v (λ ℓ → prV s x ∘ ` " : " ∘ prTm t ℓ) topᴸ atmᴸ ∘ `" → " ∘ prTm u topᴸ) topᴸ
    prTm (sort l)    = ``("Set" ++ showNat l)
    prTm (lit l)     = ``(showLiteral l)
    prTm unknown     = ``"_"
    
    prLam s b v = paren-visibility v (const (prV s b)) atmᴸ topᴸ 
    
    prLams (lam b v (abs s t)) ℓ = `" "   ∘ prLam s b v ∘ prLams t ℓ
    prLams t                   ℓ = `" → " ∘ prTm t ℓ

    prTms []                          = id
    prTms (arg (arg-info v r) x ∷ as) = `" " ∘ paren-visibility v (prTm x) appᴸ atmᴸ ∘ prTms as
    
    prTerm : ℕ → Pr Term
    prTerm k t = prTm (Level.term k t) topᴸ

    prType : ℕ → Pr Type
    prType k = prTerm k ∘ unEl

    prPats    : Prᴸ Pats
    prPattern : Prᴸ Pattern
    
    prPats []                            ℓ = id
    prPats (arg (arg-info v r) p ∷ pats) ℓ = paren-visibility v (prPattern p) appᴸ atmᴸ ∘ `" " ∘ prPats pats ℓ

    prPattern (con c pats) ℓ = `(showName' c) ∘ `" " ∘ prPats pats ℓ
    prPattern dot            = ``"._"
    prPattern (var s)        = ``(s)
    prPattern (lit l)        = ``(showLiteral l)
    prPattern (proj p)       = ``(showName' p)
    prPattern absurd         = ``"()"

    prClause : Pr Clause
    prClause (clause ps body)   =
       case (Level.pats ps 0) of λ { (ps' , Γ) → 
       prPats ps' appᴸ ∘ `" = " ∘ prTerm Γ body }
    prClause (absurd-clause ps) =
       case (Level.pats ps 0) of λ { (ps' , Γ) → 
       prPats ps' appᴸ }
    
    module _ (name : String) where
        prClauses : Pr Clauses
        prClauses cs = Data.List.map (λ c → ` name ∘ `" " ∘ prClause c) cs `sepBy` `"\n" ∘ `"\n"

        prFunDef : Pr FunctionDef
        prFunDef (fun-def ty cs) = ` name ∘ `" : " ∘ prType 0 ty ∘ `"\n" ∘ prClauses cs

    module _ (name : Name) where
        private
          sname = showName' name
          ty    = type name
        prSig : Pr String
        prSig k = ` k ∘ ` sname ∘ `" : " ∘ prType 0 ty

        prDef' : Pr Definition
        prDef' (function d)  = prFunDef sname d
        prDef' (data-type d) = prSig "data"
        prDef' (record′ d)   = prSig "record"
        prDef' constructor′  = prSig "constructor"
        prDef' axiom         = prSig "postulate"
        prDef' primitive′    = prSig "primitive"

        prDef : ShowS
        prDef = prDef' (definition name)

basename : String → String
basename = fromList ∘ reverse ∘ takeWhile (not ∘ Data.Char._==_ '.') ∘ reverse ∘ toList

showBasename : Name → String
showBasename n = basename (showName n)

open Printer showBasename

showTerm : Term → String
showTerm = showOf (prTerm 0)

showType : Type → String
showType = showTerm ∘ unEl

showClause : Clause → String
showClause = showOf prClause

showClauses : (name : String) → Clauses → String
showClauses = showOf ∘ prClauses

showFunDef : (name : String) → FunctionDef → String
showFunDef = showOf ∘ prFunDef

showDef : Name → String
showDef = showOf prDef

-- -}
-- -}
-- -}
-- -}
