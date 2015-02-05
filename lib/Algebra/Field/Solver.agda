import Algebra.Field as Field renaming (Field-Ops to RawField ; module Field-Ops to RawField)
import Algebra.RingSolver as RS

open import Relation.Binary.PropositionalEquality.NP

open import Level
open import Data.Nat as Nat using (ℕ ; suc ; zero)
open import Data.Fin
open import Data.One
open import Data.Product

open import Function

module Algebra.Field.Solver
  {f}{F : Set f}
  (𝔽 : Field.RawField F) where

module 𝔽 = Field.RawField 𝔽


data R-Op : Set where
  [+] [*] [-] : R-Op

data F-Op : Set where
  [+] [*] [-] [/] : F-Op

F-Op-eval : F-Op → F → F → F
F-Op-eval [+] x y = x 𝔽.+ y
F-Op-eval [*] x y = x 𝔽.* y
F-Op-eval [-] x y = x 𝔽.− y
F-Op-eval [/] x y = x 𝔽./ y

R-include : R-Op → F-Op
R-include [+] = [+]
R-include [*] = [*]
R-include [-] = [-]

R-Op-eval : R-Op → F → F → F
R-Op-eval op = F-Op-eval (R-include op)


data Tm (Op : Set)(m : ℕ) : Set f where
  op : (o : Op) (t₁ t₂ : Tm Op m) → Tm Op m
  con : F → Tm Op m
  var : Fin m → Tm Op m

infixl 6 _:+_ _:-_
infixl 7 _:*_ _:/_
pattern _:+_ x y = op [+] x y
pattern _:*_ x y = op [*] x y
pattern _:-_ x y = op [-] x y
pattern _:/_ x y = op [/] x y

module _ {m}{Op : Set}(evalOp : Op → F → F → F)(ρ : Fin m → F) where
  eval : Tm Op m → F
  eval (op o tm tm₁) = evalOp o (eval tm) (eval tm₁)
  eval (con x) = x
  eval (var x) = ρ x

infix 2 _/_:[_,_]
record Div {m} ρ (tm : Tm F-Op m) : Set f where
  constructor _/_:[_,_]
  field
    N : Tm R-Op m
    D : Tm R-Op m
    .nonZero-D : eval R-Op-eval ρ D ≢ 𝔽.0ᶠ
    .is-Correct : eval F-Op-eval ρ tm ≡ eval R-Op-eval ρ N 𝔽./ eval R-Op-eval ρ D

module _ (FS : Field.Field-Struct 𝔽) where
  open Field.Field-Struct FS -- {{...}}

  {-
  toRingOp : ∀ {m} → F-Op → Div {m} → Div {m} → Div {m}
  toRingOp [+] (N / D :[ P ]) (N' / D' :[ P' ]) = N :* D' :+ N' :* D  / D :* D'
                                                :[ (λ ρ → noZeroDivisor (P ρ) (P' ρ) ) ]
  toRingOp [*] (N / D :[ P ]) (N' / D' :[ P' ]) = N :* N' / D :* D' :[ (λ ρ → noZeroDivisor (P ρ) (P' ρ)) ]
  toRingOp [-] (N / D :[ P ]) (N' / D' :[ P' ]) = N :* D' :- N' :* D / D :* D'
                                                :[ (λ ρ → noZeroDivisor (P ρ) (P' ρ)) ]
  toRingOp [/] (N / D :[ P ]) (N' / D' :[ P' ]) = N :* D' / N' :* D :[ {!!} ]
  -}


  module _ {m} (ρ : Fin m → F) where
    Assumptions : Tm F-Op m → Set f
    Assumptions (op [+] tm tm₁) = Assumptions tm × Assumptions tm₁
    Assumptions (op [*] tm tm₁) = Assumptions tm × Assumptions tm₁
    Assumptions (op [-] tm tm₁) = Assumptions tm × Assumptions tm₁
    Assumptions (op [/] tm tm₁) = Assumptions tm × Assumptions tm₁ × eval F-Op-eval ρ tm₁ ≢ 0ᶠ
    Assumptions (con x) = Lift 𝟙
    Assumptions (var x) = Lift 𝟙

    toRing : ∀ (tm : Tm F-Op m) → Assumptions tm → Div {m} ρ tm
    toRing (op [+] tm tm₁) (atm , atm₁) with toRing tm atm | toRing tm₁ atm₁
    ... | N / D :[ nD , isC ] | N₁ / D₁ :[ nD₁ , isC₁ ] = N :* D₁ :+ N₁ :* D / D :* D₁
                                               :[ noZeroDivisor nD nD₁ , += isC isC₁ ∙ +-quotient nD nD₁ ]
    toRing (op [*] tm tm₁) (atm , atm₁) with toRing tm atm | toRing tm₁ atm₁
    ... | N / D :[ nD , isC ] | N₁ / D₁ :[ nD₁ , isC₁ ] = N :* N₁ / D :* D₁
                                               :[ noZeroDivisor nD nD₁ , *= isC isC₁ ∙ *-quotient nD nD₁ ]
    toRing (op [-] tm tm₁) (atm , atm₁) with toRing tm atm | toRing tm₁ atm₁
    ... | N / D :[ nD , isC ] | N₁ / D₁ :[ nD₁ , isC₁ ] = N :* D₁ :- N₁ :* D / D :* D₁
                                               :[ noZeroDivisor nD nD₁ , −= isC isC₁ ∙ −-quotient nD nD₁ ]
    toRing (op [/] tm tm₁) (atm , atm₁ , tm₁/=0) with toRing tm atm | toRing tm₁ atm₁
    ... | N / D :[ nD , isC ] | N₁ / D₁ :[ nD₁ , isC₁ ] = (N :* D₁) / (D :* N₁)
                                               :[ noZeroDivisor nD nN₁ , /= isC isC₁ ∙ /-quotient nN₁ nD nD₁ ]
      where .nN₁ : eval R-Op-eval ρ N₁ ≢ 0ᶠ
            nN₁ p = tm₁/=0 (isC₁ ∙ *= p refl ∙ 0*-zero)
    toRing (con x) _ = con x / con 𝔽.1ᶠ :[ 0≢1 ∘ !_ , ! (*= refl 1⁻¹≡1 ∙ *1-identity) ]
    toRing (var x) _ = var x / con 𝔽.1ᶠ :[ 0≢1 ∘ !_ , ! (*= refl 1⁻¹≡1 ∙ *1-identity) ]

-- -}
-- -}
-- -}
-- -}
