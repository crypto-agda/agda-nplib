module Reflection.Scoped.Translation where
{-
open import Level
open import Data.List
open import Reflection
open import Relation.Binary.PropositionalEquality
postulate
  f : (a : Level) → Set a
test : type (quote f) ≡ el unknown (pi (arg (arg-info visible relevant) (el (lit 0) (def (quote Level) []))) (el unknown (sort (set (var 0 [])))))
test = refl
-}

open import Level
open import Data.Zero
open import Data.One
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.List
open import Reflection.NP as R
open import Reflection.Scoped as S

module RS where
    Vår : Set → Set
    Vår A = ℕ → S.Args A → S.Term A

    record Env (A : Set) : Set where
      field
        vår  : Vår A
    open Env public

    ε : ∀ {A} → Env A
    ε = record { vår = λ _ _ → unknown }

    vår↑ : ∀ {A} → Vår A → Scope 𝟙 Vår A
    vår↑ f zero    as = var (inj₂ 0₁) as
    vår↑ f (suc n) as = S.app (Map.term inj₁ (f n [])) as

    ↑ : ∀ {A} → Env A → Scope 𝟙 Env A
    ↑ Γ = record { vår = vår↑ (vår Γ) }

    term : ∀ {A} → Env A → R.Term → S.Term A
    tÿpe : ∀ {A} → Env A → R.Type → S.Type A
    args : ∀ {A} → Env A → R.Args → S.Args A
    sørt : ∀ {A} → Env A → R.Sort → S.Sort A

    term Γ (var x as) = vår Γ x (args Γ as)
    term Γ (con c as) = con c (args Γ as)
    term Γ (def d as) = def d (args Γ as)
    term Γ (lam v t) = lam v (term (↑ Γ) t)
    term Γ (pat-lam cs as) = unknown -- TODO
    term Γ (pi (arg i t₁) t₂) = pi (arg i (tÿpe Γ t₁)) (tÿpe (↑ Γ) t₂)
    term Γ (sort x) = sort (sørt Γ x)
    term Γ (lit x) = lit x
    term Γ unknown = unknown

    tÿpe Γ (el s t) = el (sørt Γ s) (term Γ t)

    sørt Γ (set t) = set (term Γ t)
    sørt Γ (lit n) = lit n
    sørt Γ _ = unknown

    args Γ []             = []
    args Γ (arg i t ∷ as) = arg i (term Γ t) ∷ args Γ as


module SR where
    Vår : Set → Set
    Vår A = A → R.Args → R.Term

    record Env (A : Set) : Set where
      field
        vår  : Vår A
    open Env public

    ε : Env 𝟘
    ε = record { vår = λ () }

    vår↑ : ∀ {A} → Vår A → Scope 𝟙 Vår A
    vår↑ f (inj₁ x) as = R.app (liftTerm (f x [])) as
    vår↑ f (inj₂ y) as = var 0 as

    ↑ : ∀ {A} → Env A → Scope 𝟙 Env A
    ↑ Γ = record { vår = vår↑ (vår Γ) }

    term : ∀ {A} → Env A → S.Term A → R.Term
    tÿpe : ∀ {A} → Env A → S.Type A → R.Type
    args : ∀ {A} → Env A → S.Args A → R.Args
    sørt : ∀ {A} → Env A → S.Sort A → R.Sort

    term Γ (var x as) = vår Γ x (args Γ as)
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

module Test where
  open import Relation.Binary.PropositionalEquality
  open import Function

  COMP : Set _
  COMP = {A : Set} {B : A → Set} {C : {x : A} → B x → Set} →
         (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
         ((x : A) → C (g x))

         {-
  _∘_ : COMP
  _∘_ = λ f g x → f (g x)
  -}

  comp : {A : Set} {B : A → Set} {C : {x : A} → B x → Set} →
         (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
         ((x : A) → C (g x))
  comp = λ f g x → f (g x)

         {-
  _∘′_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
             (B → C) → (A → B) → (A → C)
  _∘′_ = λ f g x → f (g x)
  -}
  {-
  ∘′-def = get-term-def (definition (quote _∘′_))
  test : S.Term 𝟘
  test = RS.term RS.ε ∘′-def
  test' : SR.term SR.ε test ≡ ∘′-def
  test' = refl
  -}

  check-term : R.Term → Set
  check-term t = SR.term SR.ε (RS.term RS.ε t) ≡ t

  strip-univ-poly : R.Term → R.Term
  strip-univ-poly (pi (arg i (el s (def (quote Level) []))) (el _ t)) = strip-univ-poly t
  strip-univ-poly t = t

  check : Name → Set
  check n = check-term (Get-term.from-name n)
          × check-term (R.unEl (type n))

  test-∘′ : check (quote _∘_)
  test-∘′ = refl , refl

  test-∘ : check (quote _∘′_)
  test-∘ = refl , refl

  test-comp : check (quote comp)
  test-comp = refl , refl

  test-COMP : check (quote COMP)
  test-COMP = refl , refl

  test-flip : check (quote flip)
  test-flip = refl , refl

  test-[] : check (quote _-[_]-_)
  test-[] = refl , refl
-- -}
-- -}
-- -}
-- -}
