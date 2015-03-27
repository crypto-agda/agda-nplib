{-# OPTIONS --without-K #-}
open import Relation.Binary.PropositionalEquality.NP
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Function.Extensionality
open import Data.Product.NP
open import Data.Nat.NP using (ℕ; zero; fold) renaming (suc to 1+)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Algebra.Monoid
open import Algebra.Monoid.Commutative
open import Algebra.Group
open import Algebra.Group.Abelian
open import HoTT

module Algebra.Field where

record Field-Ops {ℓ} (A : Set ℓ) : Set ℓ where
  infixl 6 2+_

  field
    +-grp-ops : Group-Ops A
    *-grp-ops : Group-Ops A

  open Additive-Group-Ops       +-grp-ops public
    renaming (2⊗_ to 2*_)
  open Multiplicative-Group-Ops *-grp-ops public

  suc : A → A
  suc = _+_ 1#

  pred : A → A
  pred x = x − 1#

  2# 3# -0# -1# : A
  2#  = suc 1#
  3#  = suc 2#
  -0# = 0− 0#
  -1# = 0− 1#

  ℕ[_] : ℕ → A
  ℕ[ 0    ] = 0#
  ℕ[ 1+ n ] = fold 1# suc n

  ℤ[_] : ℤ → A
  ℤ[ + x      ] = ℕ[ x ]
  ℤ[ -[1+ x ] ] = 0− ℕ[ 1+ x ]

  -- TODO use _^⁺_ and _^_ from group/monoid
  _^ℕ_ : A → ℕ → A
  b ^ℕ 0      = 1#
  b ^ℕ (1+ e) = fold b (_*_ b) e

  _^ℤ_ : A → ℤ → A
  b ^ℤ (+ x)    = b ^ℕ x
  b ^ℤ -[1+ x ] = (b ^ℕ (1+ x))⁻¹

  2+_ : A → A
  2+ x = 2# + x

record Field-Struct {ℓ} {A : Set ℓ} (field-ops : Field-Ops A) : Set ℓ where
  open Field-Ops field-ops
  open ≡-Reasoning

  field
    0≢1                  : 0# ≢ 1#
    +-abelian-grp-struct : Abelian-Group-Struct +-grp-ops

    *-comm-mon-struct    : Commutative-Monoid-Struct *-mon-ops
    ⁻¹-inverse           : InverseNonZero 0# 1# _⁻¹ _*_
    *-+-distrs           : _*_ DistributesOver _+_

  open Additive-Abelian-Group-Struct +-abelian-grp-struct public
  -- 0−-involutive   : Involutive 0−_
  -- cancels-+-left  : LeftCancel _+_
  -- cancels-+-right : RightCancel _+_
  -- ...

  open Multiplicative-Commutative-Monoid-Struct *-comm-mon-struct public

  +-grp-struct : Group-Struct +-grp-ops
  +-grp-struct = Abelian-Group-Struct.grp-struct +-abelian-grp-struct

  +-abelian-grp : Abelian-Group A
  +-abelian-grp = +-grp-ops , +-abelian-grp-struct

  +-grp : Group A
  +-grp = +-grp-ops , +-grp-struct

  -- Since the Abelian-Group module includes all what Group and
  -- Monoid provide, we can expose a single module.
  module +-Grp = Abelian-Group +-abelian-grp

  *-mon-struct : Monoid-Struct *-mon-ops
  *-mon-struct = Commutative-Monoid-Struct.mon-struct *-comm-mon-struct

  *-mon : Monoid A
  *-mon = *-mon-ops , *-mon-struct

  *-comm-mon : Commutative-Monoid A
  *-comm-mon = *-mon-ops , *-comm-mon-struct

  module *-Mon = Commutative-Monoid *-comm-mon

  1≢0 : 1# ≢ 0#
  1≢0 e = 0≢1 (! e)

  NonZero : A → Set ℓ
  NonZero x = x ≢ 0#

  A/0 = Σ A NonZero

  ⁻¹-left-inverse : LeftInverseNonZero 0# 1# _⁻¹ _*_
  ⁻¹-left-inverse = fst ⁻¹-inverse

  ⁻¹-right-inverse : RightInverseNonZero 0# 1# _⁻¹ _*_
  ⁻¹-right-inverse = snd ⁻¹-inverse

  *-+-distr : _*_ DistributesOverˡ _+_
  *-+-distr = fst *-+-distrs

  *0-zero : RightZero 0# _*_
  *0-zero = cancels-+-right  (+= idp (! *1-identity) ∙ ! *-+-distr
                            ∙ *= idp 0+-identity ∙ *1-identity ∙ ! 0+-identity)

  0*-zero : LeftZero 0# _*_
  0*-zero = *-comm ∙ *0-zero

  c⁻¹*c*x : ∀ {c x} → c ≢ 0# → c ⁻¹ * c * x ≡ x
  c⁻¹*c*x c≢0 = *= (⁻¹-left-inverse c≢0) idp ∙ 1*-identity

  cancels-*-left : LeftCancelNonZero 0# _*_
  cancels-*-left c≢0 p = ! c⁻¹*c*x c≢0 ∙ *-!assoc= p ∙ c⁻¹*c*x c≢0

  cancels-*-right : RightCancelNonZero 0# _*_
  cancels-*-right c≢0 p = cancels-*-left c≢0 (*-comm= p)

  unique-0 : ∀ {x y} → x ≢ 0# → x * y ≡ 0# → y ≡ 0#
  unique-0 nx xy≡0 = cancels-*-left nx (xy≡0 ∙ ! *0-zero)

  no-zero-divisor : ∀ {x y} → x ≢ 0# → y ≢ 0# → x * y ≢ 0#
  no-zero-divisor nx ny x*y≡0 = ny (unique-0 nx x*y≡0)

  _*/0_ : A/0 → A/0 → A/0
  (x , x≢0) */0 (y , y≢0) = x * y , no-zero-divisor x≢0 y≢0

  1## : A/0
  1## = 1# , 1≢0

  *-mon-ops/0 : Monoid-Ops A/0
  *-mon-ops/0 = _*/0_ , 1##

  ⁻¹-non-zero : ∀ {x} → x ≢ 0# → x ⁻¹ ≢ 0#
  ⁻¹-non-zero x≢0 = λ p → 0≢1 (! 0*-zero ∙ *= (! p) idp ∙ ⁻¹-left-inverse x≢0)

  _⁻¹/0 : A/0 → A/0
  (x , x≢0) ⁻¹/0 = x ⁻¹ , ⁻¹-non-zero x≢0

  *-grp-ops/0 : Group-Ops A/0
  *-grp-ops/0 = *-mon-ops/0 , _⁻¹/0

  module _ {{_ : FunExt}} where
    A/0= : {x y : A/0}(p : fst x ≡ fst y) → x ≡ y
    A/0= p = pair= p (¬-has-all-paths _ _)

    *-mon-struct/0 : Monoid-Struct *-mon-ops/0
    *-mon-struct/0 = (A/0= *-assoc , A/0= *-!assoc)
                   , A/0= 1*-identity , A/0= *1-identity

    ⁻¹-left-inverse/0 : LeftInverse 1## _⁻¹/0 _*/0_
    ⁻¹-left-inverse/0 {x , x≢0} = A/0= (⁻¹-left-inverse x≢0)

    *-grp-struct/0 : Group-Struct *-grp-ops/0
    *-grp-struct/0 = *-mon-struct/0
                   , (λ {x} → ⁻¹-left-inverse/0 {x}) ,
                     (λ {x} → A/0= (⁻¹-right-inverse (snd x)))

    *-grp/0 : Group A/0
    *-grp/0 = *-grp-ops/0 , *-grp-struct/0

    *-abelian-grp-struct/0 : Abelian-Group-Struct *-grp-ops/0
    *-abelian-grp-struct/0 = *-grp-struct/0 , A/0= *-comm

    *-abelian-grp/0 : Abelian-Group A/0
    *-abelian-grp/0 = *-grp-ops/0 , *-abelian-grp-struct/0
    -- module *-Grp/0 = Abelian-Group *-abelian-grp/0

  0−-left-inverse : LeftInverse 0# 0−_ _+_
  0−-left-inverse = fst 0−-inverse

  0−-right-inverse : RightInverse 0# 0−_ _+_
  0−-right-inverse = snd 0−-inverse

  0−= : ∀ {x y} → x ≡ y → 0− x ≡ 0− y
  0−= = ap 0−_

  ⁻¹= : ∀ {x y} → x ≡ y → x ⁻¹ ≡ y ⁻¹
  ⁻¹= = ap _⁻¹

  *-+-distrʳ : _*_ DistributesOverʳ _+_
  *-+-distrʳ = *-comm ∙ *-+-distr ∙ += *-comm *-comm

  /-+-distrʳ : _/_ DistributesOverʳ _+_
  /-+-distrʳ = *-+-distrʳ

  0−c+c+x : ∀ {c x} → 0− c + c + x ≡ x
  0−c+c+x = += 0−-left-inverse idp ∙ 0+-identity

  -0≡0 : -0# ≡ 0#
  -0≡0 = 0−0≡0

  0≢-1 : 0# ≢ -1#
  0≢-1 0≡-1 = 0≢1 (! 0−-left-inverse ∙ +-comm ∙ ! ap suc 0≡-1 ∙ +0-identity)

  0−-*-distr : ∀ {x y} → 0−(x * y) ≡ (0− x) * y
  0−-*-distr = cancels-+-right (0−-left-inverse ∙ ! 0*-zero ∙ *= (! 0−-left-inverse) idp ∙ *-+-distrʳ)

  -1*-neg : ∀ {x} → -1# * x ≡ 0− x
  -1*-neg = ! 0−-*-distr ∙ 0−= 1*-identity

  1⁻¹≡1 : 1# ⁻¹ ≡ 1#
  1⁻¹≡1 = ! *1-identity ∙ ⁻¹-left-inverse 1≢0

  /1-id : ∀ {x} → x / 1# ≡ x
  /1-id = *= idp 1⁻¹≡1 ∙ *1-identity

  2*-spec : ∀ {n} → 2* n ≡ 2# * n
  2*-spec = ! += 1*-identity 1*-identity ∙ ! *-+-distrʳ

  *-unique-inverse : ∀ {x y} → x ≢ 0# → x * y ≡ 1# → y ≡ x ⁻¹
  *-unique-inverse x≢0 xy=1 = ! 1*-identity ∙ *= (! ⁻¹-left-inverse x≢0) idp ∙ *-assoc ∙ *= idp xy=1 ∙ *1-identity

  ⁻¹-involutive : ∀ {x} → x ≢ 0# → x ⁻¹ ⁻¹ ≡ x
  ⁻¹-involutive x≢0 = ! *-unique-inverse (⁻¹-non-zero x≢0) (⁻¹-left-inverse x≢0)

  ⁻¹*-distr : ∀ {x y} → x ≢ 0# → y ≢ 0# → (x * y)⁻¹ ≡ x ⁻¹  / y
  ⁻¹*-distr x≢0 y≢0 =
    ! (*-unique-inverse (no-zero-divisor x≢0 y≢0) (*= idp *-comm ∙ *-assoc ∙ *= idp (! *-assoc ∙ *= (⁻¹-right-inverse y≢0) idp ∙ 1*-identity) ∙ ⁻¹-right-inverse x≢0))

  +-quotient : ∀ {a b a' b'} → b ≢ 0# → b' ≢ 0#
    → (a / b) + (a' / b') ≡ (a * b' + a' * b) / (b * b')
  +-quotient b b'
    = += (*= (! *1-identity ∙ *= idp (! ⁻¹-left-inverse b') ∙ *= idp *-comm ∙ ! *-assoc) idp ∙
          *-assoc ∙ *= idp (! ⁻¹*-distr b' b ∙ ⁻¹= *-comm))
         (*= (! *1-identity ∙ *= idp (! ⁻¹-left-inverse b ) ∙ *= idp *-comm) idp ∙
          *-!assoc= *-assoc ∙ *= idp (! ⁻¹*-distr b b'))
    ∙ ! /-+-distrʳ

  −-quotient : ∀ {a b a' b'} → b ≢ 0# → b' ≢ 0#
    → (a / b) − (a' / b') ≡ (a * b' − a' * b) / (b * b')
  −-quotient b b' = += idp 0−-*-distr ∙ +-quotient b b' ∙ /= (+= idp (! 0−-*-distr)) idp

  *-quotient : ∀ {a b a' b'} → b ≢ 0# → b' ≢ 0#
    → (a / b) * (a' / b') ≡ (a * a') / (b * b')
  *-quotient b≢0 b'≢0 = *-interchange ∙ *= idp (! ⁻¹*-distr b≢0 b'≢0)

  /-quotient : ∀ {a b a' b'} → a' ≢ 0# → b ≢ 0# → b' ≢ 0#
     → (a / b) / (a' / b') ≡ (a * b') / (b * a')
  /-quotient a' b b' = *= idp (⁻¹*-distr a' (⁻¹-non-zero b') ∙ *= idp (⁻¹-involutive b') ∙ *-comm)
    ∙ *-interchange ∙ *= idp (! ⁻¹*-distr b a')

  0−-*-distr' : ∀ {x y} → 0−(x * y) ≡ x * (0− y)
  0−-*-distr' = 0−= *-comm ∙ 0−-*-distr ∙ *-comm

  *-−-distr : ∀ {x y z} → x * (y − z) ≡ x * y − x * z
  *-−-distr = *-+-distr ∙ += idp (! 0−-*-distr')

  0−-+-distr : ∀ {x y} → 0−(x + y) ≡ 0− x − y
  0−-+-distr = 0−-hom

  ²-*-distr : ∀ {x y} → (x * y)² ≡ x ² * y ²
  ²-*-distr = *-interchange

  ²-0−-distr : ∀ {x} → (0− x)² ≡ x ²
  ²-0−-distr {x} = ! 0−-*-distr ∙ 0−= (! 0−-*-distr') ∙ 0−-involutive

  2*-*-distr : ∀ {x y} → 2*(x * y) ≡ 2* x * y
  2*-*-distr = ! *-+-distrʳ

  ²-+-distr : ∀ {x y} → (x + y)² ≡ x ² + y ² + 2* x * y
  ²-+-distr {x} {y} = (x + y)²
                    ≡⟨ *-+-distr ⟩
                      (x + y) * x + (x + y) * y
                    ≡⟨ += *-+-distrʳ *-+-distrʳ ⟩
                      x ² + y * x + (x * y + y ²)
                    ≡⟨ += (+= idp *-comm) +-comm ∙ +-interchange ⟩
                      x ² + y ² + 2*(x * y)
                    ≡⟨ += idp 2*-*-distr ⟩
                       x ² + y ² + 2* x * y
                    ∎

  ²-−-distr : ∀ {x y} → (x − y)² ≡ x ² + y ² − 2* x * y
  ²-−-distr = ²-+-distr ∙ += (+= idp ²-0−-distr) (*-comm ∙ ! 0−-*-distr ∙ 0−= *-comm)

record Field {ℓ} (A : Set ℓ) : Set ℓ where
  field
    field-ops    : Field-Ops A
    field-struct : Field-Struct field-ops
  open Field-Ops    field-ops    public
  open Field-Struct field-struct public
-- -}
-- -}
-- -}
-- -}
-- -}
