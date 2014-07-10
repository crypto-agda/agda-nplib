module Algebra.Field where

open import Relation.Binary.PropositionalEquality.NP
import Algebra.FunctionProperties.Eq as FP
open import Data.Nat.NP using (ℕ; zero; suc; fold)
import Data.Integer as ℤ
open ℤ using (ℤ)

record Field-Ops {ℓ} (A : Set ℓ) : Set ℓ where
  infixl 6 _+_ _−_
  infixl 7 _*_ _/_ 2*_

  field
    _+_ _*_     : A → A → A
    0ᶠ 1ᶠ        : A
    0-_         : A → A
    _⁻¹         : A → A

  _−_ _/_ : A → A → A
  a − b = a + 0- b
  a / b = a * b ⁻¹

  sucᶠ : A → A
  sucᶠ = _+_ 1ᶠ

  predᶠ : A → A
  predᶠ x = x − 1ᶠ

  2ᶠ 3ᶠ -0ᶠ -1ᶠ : A
  2ᶠ  = sucᶠ 1ᶠ
  3ᶠ  = sucᶠ 2ᶠ
  -0ᶠ = 0- 0ᶠ
  -1ᶠ = 0- 1ᶠ

  ℕ[_] : ℕ → A
  ℕ[ 0     ] = 0ᶠ
  ℕ[ suc n ] = fold 1ᶠ sucᶠ n

  ℤ[_] : ℤ → A
  ℤ[ ℤ.+ x      ] = ℕ[ x ]
  ℤ[ ℤ.-[1+ x ] ] = 0- ℕ[ suc x ]

  _^ℕ_ : A → ℕ → A
  b ^ℕ 0       = 1ᶠ
  b ^ℕ (suc e) = fold b (_*_ b) e

  _^ℤ_ : A → ℤ → A
  b ^ℤ (ℤ.+ x)    = b ^ℕ x
  b ^ℤ ℤ.-[1+ x ] = (b ^ℕ (suc x))⁻¹

  2+_ : A → A
  2+ x = 2ᶠ + x

  2*_ : A → A
  2* x = x + x

  _² : A → A
  x ² = x * x

  _³ : A → A
  x ³ = x ² * x

record Field-Struct {ℓ} {A : Set ℓ} (field-ops : Field-Ops A) : Set ℓ where
  open FP {ℓ} {A}
  open Field-Ops field-ops
  open ≡-Reasoning

  field
    0≢1         : 0ᶠ ≢ 1ᶠ
    +-assoc     : Associative _+_
    *-assoc     : Associative _*_
    +-comm      : Commutative _+_
    *-comm      : Commutative _*_
    0+-identity : LeftIdentity 0ᶠ _+_
    1*-identity : LeftIdentity 1ᶠ _*_
    0--inverse  : LeftInverse 0ᶠ 0-_ _+_
    ⁻¹-inverse  : LeftInverseNonZero 0ᶠ 1ᶠ _⁻¹ _*_
    *-+-distr   : _*_ DistributesOverˡ _+_

  0--right-inverse : RightInverse 0ᶠ 0-_ _+_
  0--right-inverse = +-comm ∙ 0--inverse

  ⁻¹-right-inverse : RightInverseNonZero 0ᶠ 1ᶠ _⁻¹ _*_
  ⁻¹-right-inverse p = *-comm ∙ ⁻¹-inverse p

  +0-identity : RightIdentity 0ᶠ _+_
  +0-identity = +-comm ∙ 0+-identity

  *1-identity : RightIdentity 1ᶠ _*_
  *1-identity = *-comm ∙ 1*-identity

  += : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x + y ≡ x' + y'
  += {x} {y' = y'} p q = ap (_+_ x) q ∙ ap (λ z → z + y') p

  *= : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x * y ≡ x' * y'
  *= {x} {y' = y'} p q = ap (_*_ x) q ∙ ap (λ z → z * y') p

  −= : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x − y ≡ x' − y'
  −= {x} {y' = y'} p q = ap (_−_ x) q ∙ ap (λ z → z − y') p

  /= : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x / y ≡ x' / y'
  /= {x} {y' = y'} p q = ap (_/_ x) q ∙ ap (λ z → z / y') p

  0-= : ∀ {x x'} → x ≡ x' → 0- x ≡ 0- x'
  0-= = ap 0-_

  +-*-distr : _*_ DistributesOverʳ _+_
  +-*-distr = *-comm ∙ *-+-distr ∙ += *-comm *-comm

  +-/-distr : _/_ DistributesOverʳ _+_
  +-/-distr = +-*-distr

  0-c+c+x : ∀ {c x} → 0- c + c + x ≡ x
  0-c+c+x = += 0--inverse refl ∙ 0+-identity

  +-left-cancel : LeftCancel _+_
  +-left-cancel p = ! 0-c+c+x ∙ +-assoc
                  ∙ ap (λ z → 0- _ + z) p
                  ∙ ! +-assoc ∙ 0-c+c+x

  +-right-cancel : RightCancel _+_
  +-right-cancel p = +-left-cancel (+-comm ∙ p ∙ +-comm)

  -0≡0 : -0ᶠ ≡ 0ᶠ
  -0≡0 = +-left-cancel (0--right-inverse ∙ ! 0+-identity)

  0≢-1 : 0ᶠ ≢ -1ᶠ
  0≢-1 0≡-1 = 0≢1 (! 0--inverse ∙ +-comm ∙ ! ap sucᶠ 0≡-1 ∙ +0-identity)

  c⁻¹*c*x : ∀ {c x} → c ≢ 0ᶠ → c ⁻¹ * c * x ≡ x
  c⁻¹*c*x c≢0 = *= (⁻¹-inverse c≢0) refl ∙ 1*-identity

  *-left-cancel : LeftCancelNonZero 0ᶠ _*_
  *-left-cancel c≢0 p = ! c⁻¹*c*x c≢0 ∙ *-assoc
                      ∙ ap (λ z → _ ⁻¹ * z) p
                      ∙ ! *-assoc ∙ c⁻¹*c*x c≢0

  *-right-cancel : RightCancelNonZero 0ᶠ _*_
  *-right-cancel c≢0 p = *-left-cancel c≢0 (*-comm ∙ p ∙ *-comm)

  *0-zero : RightZero 0ᶠ _*_
  *0-zero = +-right-cancel  (+= refl (! *1-identity) ∙ ! *-+-distr
                            ∙ *= refl 0+-identity ∙ *1-identity ∙ ! 0+-identity)

  0*-zero : LeftZero 0ᶠ _*_
  0*-zero = *-comm ∙ *0-zero

  ⁻¹-notZero : ∀ {x} → x ≢ 0ᶠ → x ⁻¹ ≢ 0ᶠ
  ⁻¹-notZero x/=0 = λ p → 0≢1 (! 0*-zero ∙ *= (! p) refl ∙ ⁻¹-inverse x/=0)

  0--*-distr : ∀ {x y} → 0- (x * y) ≡ (0- x) * y
  0--*-distr = +-right-cancel (0--inverse ∙ ! 0*-zero ∙ *= (! 0--inverse) refl ∙ +-*-distr)

  -1*-neg : ∀ {x} → -1ᶠ * x ≡ 0- x
  -1*-neg = ! 0--*-distr ∙ 0-= 1*-identity


  0--involutive : Involutive 0-_
  0--involutive = +-left-cancel (0--right-inverse ∙ ! 0--inverse)


  1⁻¹≡1 : 1ᶠ ⁻¹ ≡ 1ᶠ
  1⁻¹≡1 = ! *1-identity ∙ ⁻¹-inverse (λ p → 0≢1 (! p))

  noZeroDivisor : ∀ {x y} → x ≢ 0ᶠ → y ≢ 0ᶠ → x * y ≢ 0ᶠ
  noZeroDivisor nx ny x*y≡0ᶠ = ny (! *1-identity ∙ *= refl (! ⁻¹-inverse nx)
                                   ∙ *= refl *-comm ∙ ! *-assoc
                                   ∙ *= (*-comm ∙ x*y≡0ᶠ) refl ∙ 0*-zero
                                   )

  2*-spec : ∀ {n} → 2* n ≡ 2ᶠ * n
  2*-spec = ! += 1*-identity 1*-identity ∙ ! +-*-distr

  +-interchange : Interchange _+_ _+_
  +-interchange = InterchangeFromAssocComm.·-interchange _+_ +-assoc +-comm

  *-interchange : Interchange _*_ _*_
  *-interchange = InterchangeFromAssocComm.·-interchange _*_ *-assoc *-comm

  *-unique-inverse : ∀ {x y} → x ≢ 0ᶠ → x * y ≡ 1ᶠ → y ≡ x ⁻¹
  *-unique-inverse x/=0 xy=1 = ! 1*-identity ∙ *= (! ⁻¹-inverse x/=0) refl ∙ *-assoc ∙ *= refl xy=1 ∙ *1-identity

  ⁻¹-involutive : ∀ {x} → x ≢ 0ᶠ → x ⁻¹ ⁻¹ ≡ x
  ⁻¹-involutive x/=0 = ! *-unique-inverse (⁻¹-notZero x/=0) (⁻¹-inverse x/=0)

  ⁻¹*-distr : ∀ {x y} → x ≢ 0ᶠ → y ≢ 0ᶠ → (x * y)⁻¹ ≡ x ⁻¹  / y
  ⁻¹*-distr x/=0 y/=0 =
    ! (*-unique-inverse (noZeroDivisor x/=0 y/=0) (*= refl *-comm ∙ *-assoc ∙ *= refl (! *-assoc ∙ *= (⁻¹-right-inverse y/=0) refl ∙ 1*-identity) ∙ ⁻¹-right-inverse x/=0))

  +-quotient : ∀ {a b a' b'} → b ≢ 0ᶠ → b' ≢ 0ᶠ
    →(a / b) + (a' / b') ≡ (a * b' + a' * b) / (b * b')
  +-quotient b b'
    = += (/= (! *1-identity ∙ *= refl (! ⁻¹-inverse b')) refl) (/= (! *1-identity ∙ *= refl (! ⁻¹-inverse b)) refl)
    ∙ (+= (/= (*= refl *-comm) refl) (/= (*= refl *-comm) refl)
    ∙ += (*= (! *-assoc) refl ∙ *-assoc ∙ *= refl (! ⁻¹*-distr b' b ∙ ap _⁻¹ *-comm)) (*-assoc ∙ *= refl *-assoc ∙ ! *-assoc ∙ *= refl (! ⁻¹*-distr b b') ))
    ∙ ! +-/-distr

  −-quotient : ∀ {a b a' b'} → b ≢ 0ᶠ → b' ≢ 0ᶠ
    → (a / b) − (a' / b') ≡ (a * b' − a' * b) / (b * b')
  −-quotient b b' = += refl 0--*-distr ∙ +-quotient b b' ∙ /= (+= refl (! 0--*-distr)) refl

  *-quotient : ∀ {a b a' b'} → b ≢ 0ᶠ → b' ≢ 0ᶠ
    → (a / b) * (a' / b') ≡ (a * a') / (b * b')
  *-quotient b/=0 b'/=0 = *-assoc ∙ *= refl (! *-assoc ∙ *= *-comm refl ∙ *-assoc) ∙ ! *-assoc ∙ *= refl (! ⁻¹*-distr b/=0 b'/=0)

  /-quotient : ∀ {a b a' b'} → a' ≢ 0ᶠ → b ≢ 0ᶠ → b' ≢ 0ᶠ
     → (a / b) / (a' / b') ≡ (a * b') / (b * a')
  /-quotient a' b b' = *= refl (⁻¹*-distr a' (⁻¹-notZero b') ∙ *= refl (⁻¹-involutive b') ∙ *-comm)
    ∙ *-interchange ∙ *= refl (! ⁻¹*-distr b a')

  0--*-distr' : ∀ {x y} → 0-(x * y) ≡ x * (0- y)
  0--*-distr' = ap 0-_ *-comm ∙ 0--*-distr ∙ *-comm

  *-−-distr : ∀ {x y z} → x * (y − z) ≡ x * y − x * z
  *-−-distr = *-+-distr ∙ += refl (! 0--*-distr')

  0--+-distr : ∀ {x y} → 0-(x + y) ≡ 0- x − y
  0--+-distr =
      +-left-cancel
         (0--right-inverse
          ∙ (! 0+-identity ∙ += (! 0--right-inverse)
                                (! 0--right-inverse))
                           ∙ +-interchange)

  ²-*-distr : ∀ {x y} → (x * y)² ≡ x ² * y ²
  ²-*-distr = *-interchange

  0--cancel : ∀ {x y} → 0- x ≡ 0- y → x ≡ y
  0--cancel {x} {y} p = *-left-cancel (λ e → 0≢-1 (! e)) (-1*-neg ∙ p ∙ ! -1*-neg)

  ²-0--distr : ∀ {x} → (0- x)² ≡ x ²
  ²-0--distr {x} = ! 0--*-distr ∙ ap 0-_ (! 0--*-distr') ∙ 0--involutive

  2*-*-distr : ∀ {x y} → 2*(x * y) ≡ 2* x * y
  2*-*-distr = ! +-*-distr

  ²-+-distr : ∀ {x y} → (x + y)² ≡ x ² + y ² + 2* x * y
  ²-+-distr {x} {y} = (x + y)²
                    ≡⟨ *-+-distr ⟩
                      (x + y) * x + (x + y) * y
                    ≡⟨ += +-*-distr +-*-distr ⟩
                      x ² + y * x + (x * y + y ²)
                    ≡⟨ += (+= refl *-comm) +-comm ∙ +-interchange ⟩
                      x ² + y ² + 2*(x * y)
                    ≡⟨ += refl 2*-*-distr ⟩
                       x ² + y ² + 2* x * y
                    ∎

  ²-−-distr : ∀ {x y} → (x − y)² ≡ x ² + y ² − 2* x * y
  ²-−-distr = ²-+-distr ∙ += (+= refl ²-0--distr) (*-comm ∙ ! 0--*-distr ∙ ap 0-_ *-comm)

  open Field-Ops field-ops public

record Field {ℓ} (A : Set ℓ) : Set ℓ where
  field
    field-ops    : Field-Ops A
    field-struct : Field-Struct field-ops
  open Field-Struct field-struct public

open import Reflection.NP
open import Data.List
open import Data.Maybe.NP

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
-- -}
-- -}
-- -}
-- -}
-- -}
