import Algebra.Field as Field
import Algebra.RingSolver as RS

open import Relation.Binary.PropositionalEquality.NP

open import Level
open import Data.Nat as Nat using (ℕ)
open import Data.Fin
open import Data.One
open import Data.Product

open import Function

module Algebra.Field.Solver where

data R-Op : Set where
  [+] [*] [-] : R-Op

data F-Op : Set where
  [+] [*] [-] [/] : F-Op

data Tm (F Op Var : Set) : Set where
  op  : (o : Op) (t₁ t₂ : Tm F Op Var) → Tm F Op Var
  con : F → Tm F Op Var
  var : Var → Tm F Op Var

infixl 6 _:+_ _:-_
infixl 7 _:*_ _:/_
pattern _:+_ x y = op [+] x y
pattern _:*_ x y = op [*] x y
pattern _:-_ x y = op [-] x y
pattern _:/_ x y = op [/] x y

R-include : R-Op → F-Op
R-include [+] = [+]
R-include [*] = [*]
R-include [-] = [-]

module _ {F Op Var : Set}(evalOp : Op → F → F → F)(ρ : Var → F) where
  eval : Tm F Op Var → F
  eval (op o t u) = evalOp o (eval t) (eval u)
  eval (con x) = x
  eval (var x) = ρ x

module _
  {Var : Set}
  {F : Set}
  (𝔽 : Field.Field-Ops F)
  where

  module 𝔽 = Field.Field-Ops 𝔽

  F-Op-eval : F-Op → F → F → F
  F-Op-eval [+] x y = x 𝔽.+ y
  F-Op-eval [*] x y = x 𝔽.* y
  F-Op-eval [-] x y = x 𝔽.− y
  F-Op-eval [/] x y = x 𝔽./ y

  R-Op-eval : R-Op → F → F → F
  R-Op-eval o = F-Op-eval (R-include o)

  evalF : (ρ : Var → F) → Tm F F-Op Var → F
  evalR : (ρ : Var → F) → Tm F R-Op Var → F
  evalF = eval F-Op-eval
  evalR = eval R-Op-eval

  infix 2 _/_:[_,_]
  record Div ρ (t : Tm F F-Op Var) : Set where
    constructor _/_:[_,_]
    field
      N : Tm F R-Op Var
      D : Tm F R-Op Var
      .non-zero-D : evalR ρ D ≢ 𝔽.`0
      .is-correct : evalF ρ t ≡ evalR ρ N 𝔽./ evalR ρ D

  module _ (FS : Field.Field-Struct 𝔽)(ρ : Var → F) where
    open Field.Field-Struct FS

    private
      TmF = Tm F F-Op Var
      TmR = Tm F R-Op Var

      Div' = Div ρ
      ev = evalF ρ

    _+Div_ : ∀ {t u} → Div' t → Div' u → Div' (t :+ u)
    (N / D :[ nD , ok ]) +Div (N₁ / D₁ :[ nD₁ , ok₁ ])
       = N :* D₁ :+ N₁ :* D / D :* D₁
       :[ no-zero-divisor nD nD₁ , += ok ok₁ ∙ +-quotient nD nD₁ ]

    _*Div_ : ∀ {t u} → Div' t → Div' u → Div' (t :* u)
    (N / D :[ nD , ok ]) *Div (N₁ / D₁ :[ nD₁ , ok₁ ])
       = N :* N₁ / D :* D₁
       :[ no-zero-divisor nD nD₁ , *= ok ok₁ ∙ *-quotient nD nD₁ ]

    _−Div_ : ∀ {t u} → Div' t → Div' u → Div' (t :- u)
    (N / D :[ nD , ok ]) −Div (N₁ / D₁ :[ nD₁ , ok₁ ])
       = N :* D₁ :- N₁ :* D / D :* D₁
       :[ no-zero-divisor nD nD₁ , −= ok ok₁ ∙ −-quotient nD nD₁ ]

    _/Div_:[_] : ∀ {t u} → Div' t → Div' u → ev u ≢ `0 → Div' (t :/ u)
    (N / D :[ nD , ok ]) /Div (N₁ / D₁ :[ nD₁ , ok₁ ]) :[ u≢0 ]
      = (N :* D₁) / (D :* N₁)
      :[ no-zero-divisor nD nN₁ , /= ok ok₁ ∙ /-quotient nN₁ nD nD₁ ]
      where .nN₁ : evalR ρ N₁ ≢ `0
            nN₁ p = u≢0 (ok₁ ∙ *= p idp ∙ 0*-zero)

    -- con-Div and var-Div are basically the same but not so convenient to unify
    con-Div : ∀ x → Div' (con x)
    var-Div : ∀ x → Div' (var x)

    con-Div x = con x / con 𝔽.`1 :[ 1≢0 , ! /1-id ]
    var-Div x = var x / con 𝔽.`1 :[ 1≢0 , ! /1-id ]

    Assumptions : TmF → Set
    Assumptions (op [+] t u) = Assumptions t × Assumptions u
    Assumptions (op [*] t u) = Assumptions t × Assumptions u
    Assumptions (op [-] t u) = Assumptions t × Assumptions u
    Assumptions (op [/] t u) = Assumptions t × Assumptions u × ev u ≢ `0
    Assumptions (con x) = Lift 𝟙
    Assumptions (var x) = Lift 𝟙

    to-ring : ∀ (t : TmF) → Assumptions t → Div' t
    to-ring (op [+] t u) (at , au)       = to-ring t at +Div to-ring u au
    to-ring (op [*] t u) (at , au)       = to-ring t at *Div to-ring u au
    to-ring (op [-] t u) (at , au)       = to-ring t at −Div to-ring u au
    to-ring (op [/] t u) (at , au , u≢0) = to-ring t at /Div to-ring u au :[ u≢0 ]
    to-ring (con x) _                    = con-Div x
    to-ring (var x) _                    = var-Div x

-- -}
-- -}
-- -}
-- -}
