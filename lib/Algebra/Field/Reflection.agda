open import Reflection.NP
open import Reflection.Decode
open import Data.List
open import Data.Maybe.NP
open import Algebra.Field
open import Relation.Binary.PropositionalEquality

module Algebra.Field.Reflection where

module TermField {a} {A : Set a} (F : Field A) where
  open Field F
  pattern _`+_ t u = con (quote _+_) (argᵛʳ t ∷ argᵛʳ u ∷ [])
  pattern _`*_ t u = con (quote _*_) (argᵛʳ t ∷ argᵛʳ u ∷ [])
  pattern `0-_ t = conᵛʳ (quote 0-_) t
  pattern _`⁻¹ t = conᵛʳ (quote _⁻¹) t
  pattern `0ᶠ = con (quote 0ᶠ) []
  pattern `1ᶠ = con (quote 1ᶠ) []

  module Decode-RawField {b}{B : Set b}(G : Field-Ops B)(default : Decode-Term B) where
    module G = Field-Ops G
    decode-Field : Decode-Term B
    decode-Field `0ᶠ = just G.0ᶠ
    decode-Field `1ᶠ = just G.1ᶠ
    decode-Field (t `⁻¹) = map? G._⁻¹ (decode-Field t)
    decode-Field (`0- t) = map? G.0-_ (decode-Field t)
    decode-Field (t `+ u) = ⟪ G._+_ · decode-Field t · decode-Field u ⟫?
    decode-Field (t `* u) = ⟪ G._*_ · decode-Field t · decode-Field u ⟫?
    decode-Field t = default t

open ≡-Reasoning
open import Data.List

infixl 6 _+'_
infixl 7 _*'_
data Tm (A : Set) : Set where
  lit       : (n : ℤ) → Tm A
  var       : (x : A) → Tm A
  _+'_ _*'_ : Tm A → Tm A → Tm A

pattern  0' = lit (ℤ.+ 0)
pattern  1' = lit (ℤ.+ 1)
pattern  2' = lit (ℤ.+ 1)
pattern  3' = lit (ℤ.+ 1)
pattern -1' = lit ℤ.-[1+ 0 ]
pattern -2' = lit ℤ.-[1+ 1 ]
pattern -3' = lit ℤ.-[1+ 2 ]

record Var (A : Set) : Set where
  constructor _^'_
  field
    v : A
    e : ℤ

data Nf' (A : Set) : Set where
  _*'_ : (n : ℤ) (vs : List (Var A)) → Nf' A

data Nf (A : Set) : Set where
  _+'_ : (n : ℤ) (ts' : List (Nf' A)) → Nf A

module _ {A : Set} where
    infixl 6 _+ᴺ_

    litᴺ : ℤ → Nf A
    litᴺ n = n +' []

    varᴺ : (x : A) → Nf A
    varᴺ x = ℤ.+ 0 +' (ℤ.+ 1 *' (x ^' (ℤ.+ 1) ∷ []) ∷ [])

    _+ᴺ_ : Nf A → Nf A → Nf A
    (n +' ts) +ᴺ (m +' us) = n ℤ.+ m +' (ts ++ us)

    infixl 7 _**_ _***_ _*ᴺ_
    _**_ : ℤ → List (Nf' A) → Nf A
    z ** [] = z +' []
    m ** (n *' vs ∷ ts) with m ** ts
    ... | z +' us = z +' ((m ℤ.* n) *' vs ∷ us)

    _***_ : List (Nf' A) → List (Nf' A) → Nf A
    ts *** us = ℤ.+ 0 +' (ts ++ us)

    _*ᴺ_ : Nf A → Nf A → Nf A
    (n +' ts) *ᴺ (m +' us) =
       n ℤ.* m +' [] +ᴺ n ** us +ᴺ m ** ts +ᴺ ts *** us

module Normalizer {F : Set}
                  (F-field : Field F) where
    open Field F-field renaming (0-_ to -_)

    module _ {A : Set} where
        eval : (A → F) → Tm A → F
        eval ρ (lit x) = ℤ[ x ]
        eval ρ (t +' t₁) = eval ρ t + eval ρ t₁
        eval ρ (t *' t₁) = eval ρ t * eval ρ t₁
        eval ρ (var x)  = ρ x

        norm™ : Tm A → Nf A
        norm™ (lit x) = litᴺ x
        norm™ (var x) = varᴺ x
        norm™ (t +' t₁) = norm™ t +ᴺ norm™ t₁
        norm™ (t *' t₁) = norm™ t *ᴺ norm™ t₁

        _+''_ : Tm A → Tm A → Tm A
        -- lit (ℤ.+ 0) +'' u = u
        t +'' lit (ℤ.+ 0) = t
        t +'' u = t +' u

        _*''_ : Tm A → Tm A → Tm A
        -- lit (ℤ.+ 0) *'' u = lit (ℤ.+ 0)
        -- lit (ℤ.-[1+_] 0) *'' u = lit (ℤ.+ 0)
        t *'' lit (ℤ.+ 0) = lit (ℤ.+ 0)
        t *'' lit (ℤ.-[1+_] 0) = lit (ℤ.+ 0)
        -- lit (ℤ.+ 1) *'' u = u
        t *'' lit (ℤ.+ 1) = t
        t *'' u           = t *' u

        reifyVar : Var A → Tm A
        reifyVar (v ^' (ℤ.+ n))    = fold (lit (ℤ.+ 1)) (λ x → var v *'' x) n
        reifyVar (v ^' ℤ.-[1+ n ]) = fold (lit (ℤ.-[1+_] 1)) (λ x → var v *'' x) n

        reifyNf' : Nf' A → Tm A
        reifyNf' (n *' vs) = foldr (λ v t → reifyVar v *'' t) (lit n) vs

        reifyNf : Nf A → Tm A
        reifyNf (n +' ts') = foldr (λ n t → reifyNf' n +'' t) (lit n) ts'

        module _ ρ where
            _∼_ : (t u : Tm A) → Set
            t ∼ u = eval ρ t ≡ eval ρ u

            +'∼+'' : ∀ t u → (t +' u) ∼ (t +'' u)
            +'∼+'' t (lit (ℤ.+ zero)) = +0-identity
            +'∼+'' t (lit (ℤ.+ (suc x))) = refl
            +'∼+'' t (lit ℤ.-[1+ x ]) = refl
            +'∼+'' t (var x) = refl
            +'∼+'' t (u +' u₁) = refl
            +'∼+'' t (u *' u₁) = refl

            {-
            +-reifyNf : ∀ t u → reifyNf (t +ᴺ u) ∼ (reifyNf t +' reifyNf u)
            +-reifyNf (n +' ts') (n₁ +' ts'') = {!!}

            *-reifyNf : ∀ t u → reifyNf (t *ᴺ u) ∼ (reifyNf t *' reifyNf u)
            *-reifyNf t u = {!!}

            pf : ∀ t → eval ρ (reifyNf (norm™ t)) ≡ eval ρ t
            pf (lit n) = refl
            pf (var x) = refl
            pf (t +' t₁) rewrite +-reifyNf (norm™ t) (norm™ t₁) | pf t | pf t₁ = refl
            pf (t *' t₁) rewrite *-reifyNf (norm™ t) (norm™ t₁) | pf t | pf t₁ = refl
            -}

