{-# OPTIONS --without-K #-}
open import Relation.Binary.PropositionalEquality.NP
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Function.Extensionality using (FunExt)
open import Data.Product.NP using (Σ; _,_; fst; snd)
open import Algebra.Raw
open import Algebra.Monoid
open import Algebra.Group
open import Algebra.Group.Abelian
open import Algebra.Ring
open import Algebra.Ring.Commutative
open import HoTT

module Algebra.Field where

record Field-Struct {ℓ} {A : Set ℓ} (field-ops : Field-Ops A) : Set ℓ where
  inductive -- NO_ETA
  open Field-Ops field-ops

  open ≡-Reasoning

  field
    comm-rng-struct : Commutative-Ring-Struct rng-ops
    0≢1             : 0# ≢ 1#
    ⁻¹-inverse      : InverseNonZero 0# 1# _⁻¹ _*_

  open Commutative-Ring-Struct comm-rng-struct public
    hiding (module +*-Ring)

  comm-ring : Commutative-Ring A
  comm-ring = rng-ops , comm-rng-struct

  -- module +*-Ring = Commutative-Ring comm-ring

  1≢0 : 1# ≢ 0#
  1≢0 e = 0≢1 (! e)

  NonZero : A → Set ℓ
  NonZero x = x ≢ 0#

  A/0 = Σ A NonZero

  ⁻¹-left-inverse : LeftInverseNonZero 0# 1# _⁻¹ _*_
  ⁻¹-left-inverse = fst ⁻¹-inverse

  ⁻¹-right-inverse : RightInverseNonZero 0# 1# _⁻¹ _*_
  ⁻¹-right-inverse = snd ⁻¹-inverse

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

  /-+-distrʳ : _/_ DistributesOverʳ _+_
  /-+-distrʳ = *-+-distrʳ

  0≢-1 : 0# ≢ -1#
  0≢-1 0≡-1 = 0≢1 (! 0−-inverseˡ ∙ +-comm ∙ ! ap suc 0≡-1 ∙ +0-identity)

  1⁻¹≡1 : 1# ⁻¹ ≡ 1#
  1⁻¹≡1 = ! *1-identity ∙ ⁻¹-left-inverse 1≢0

  /1-id : ∀ {x} → x / 1# ≡ x
  /1-id = *= idp 1⁻¹≡1 ∙ *1-identity

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

record Field {ℓ} (A : Set ℓ) : Set ℓ where
  inductive -- NO_ETA
  constructor _,_
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
