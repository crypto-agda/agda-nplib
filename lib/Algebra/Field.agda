module Algebra.Field where

open import Relation.Binary.PropositionalEquality.NP
import Algebra.FunctionProperties.Eq as FP

record IsField {ℓ} (A : Set ℓ) : Set ℓ where
  open FP {ℓ} {A}

  infixl 6 _+_ _−_
  infixl 7 _*_ _/_

  field
    _+_ _*_     : A → A → A
    +-assoc     : Associative _+_
    *-assoc     : Associative _*_
    +-comm      : Commutative _+_
    *-comm      : Commutative _*_
    0ᶠ 1ᶠ        : A
    0≢1         : 0ᶠ ≢ 1ᶠ
    0+-identity : LeftIdentity 0ᶠ _+_
    1*-identity : LeftIdentity 1ᶠ _*_
    0-_         : A → A
    0--inverse  : LeftInverse 0ᶠ 0-_ _+_
    _⁻¹         : A → A
    ⁻¹-inverse  : LeftInverse 1ᶠ _⁻¹ _*_
    *-+-distr   : _*_ DistributesOverˡ _+_

  _−_ _/_ : A → A → A
  a − b = a + 0- b
  a / b = a * b ⁻¹

  0--right-inverse : RightInverse 0ᶠ 0-_ _+_
  0--right-inverse = +-comm ∙ 0--inverse

  +0-identity : RightIdentity 0ᶠ _+_
  +0-identity = +-comm ∙ 0+-identity

  *1-identity : RightIdentity 1ᶠ _*_
  *1-identity = *-comm ∙ 1*-identity

  += : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x + y ≡ x' + y'
  += {x} {y' = y'} p q = ap (_+_ x) q ∙ ap (λ z → z + y') p

  *= : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x * y ≡ x' * y'
  *= {x} {y' = y'} p q = ap (_*_ x) q ∙ ap (λ z → z * y') p

  0-c+c+x : ∀ {c x} → 0- c + c + x ≡ x
  0-c+c+x = += 0--inverse refl ∙ 0+-identity

  +-left-cancel : LeftCancel _+_
  +-left-cancel p = ! 0-c+c+x ∙ +-assoc
                  ∙ ap (λ z → 0- _ + z) p
                  ∙ ! +-assoc ∙ 0-c+c+x

  +-right-cancel : RightCancel _+_
  +-right-cancel p = +-left-cancel (+-comm ∙ p ∙ +-comm)

  0--involutive : Involutive 0-_
  0--involutive = +-left-cancel (0--right-inverse ∙ ! 0--inverse)

open import Reflection.NP
open import Data.List
open import Data.Maybe.NP

module TermField {a} {A : Set a} (F : IsField A) where
  open IsField F
  pattern _`+_ t u = con (quote _+_) (argᵛʳ t ∷ argᵛʳ u ∷ [])
  pattern _`*_ t u = con (quote _*_) (argᵛʳ t ∷ argᵛʳ u ∷ [])
  pattern `0-_ t = conᵛʳ (quote 0-_) t
  pattern _`⁻¹ t = conᵛʳ (quote _⁻¹) t
  pattern `0ᶠ = con (quote 0ᶠ) []
  pattern `1ᶠ = con (quote 1ᶠ) []

  module Decode-Field {b}{B : Set b}(G : IsField B)(default : Decode-Term B) where
    module G = IsField G
    decode-Field : Decode-Term B
    decode-Field `0ᶠ = just G.0ᶠ
    decode-Field `1ᶠ = just G.1ᶠ
    decode-Field (t `⁻¹) = map? G._⁻¹ (decode-Field t)
    decode-Field (`0- t) = map? G.0-_ (decode-Field t)
    decode-Field (t `+ u) = ⟪ G._+_ · decode-Field t · decode-Field u ⟫?
    decode-Field (t `* u) = ⟪ G._*_ · decode-Field t · decode-Field u ⟫?
    decode-Field t = default t

-- -}
-- -}
-- -}
-- -}
-- -}
